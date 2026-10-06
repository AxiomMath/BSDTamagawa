/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Covariance.LocalNegLarge
public import BSDTamagawa.LocalDensity.TailConstantBound
public import BSDTamagawa.NumberTheory.TateRunInvariance

/-!
# Ingredients of the covariance decay bound

For distinct primes `ℓ ≠ ℓ'`, let `C_p(ℓ, ℓ') = localCov p ℓ ℓ'` be the local covariance at `p`.
The covariance decay bound asks, assuming `WeierstrassCurve.HasLocalCovInputs q` at every prime
`q`, for an absolute constant `C > 0` with

  `∑_{p ∈ 𝒫} |C_p(ℓ, ℓ')| ≤ C/(ℓℓ')²`  for every pair of distinct primes `ℓ ≠ ℓ'`,

the series converging absolutely. This file does not assemble that bound; it proves the
ingredients `|C_p(ℓ, ℓ')| ≤ μ_{p,ℓ} μ_{p,ℓ'}`, the marginal bound `μ_{p,r} ≤ B(r) p^{-2}` with
`B(r) r² ≤ 504` at every prime `r`, and the convergence of `∑_p p^{-2}`, and it verifies the
hypothesis at every prime `q ≥ 5`.

## Main definitions

* `WeierstrassCurve.momentDecay`: the factor `B(r)` of the marginal bound.
* `WeierstrassCurve.primeInvSqSum`: the sum `∑_p p^{-2}`.

## Main results

* `WeierstrassCurve.valuationMoment_le_fiftysix`: `μ_{p,r} ≤ 56 p^{-2}` for all primes `p, r`.
* `WeierstrassCurve.valuationMoment_le_sharp`: `μ_{p,r} ≤ (2r + 2) p^{-r}` for a prime `r ≥ 5`.
* `WeierstrassCurve.momentDecay_mul_sq_le`: `B(r) r² ≤ 504`.
* `WeierstrassCurve.abs_localCov_le_valuationMoment_mul`: `|C_p(ℓ, ℓ')| ≤ μ_{p,ℓ} μ_{p,ℓ'}`.
* `WeierstrassCurve.hasLocalCovInputs_of_five_le`: `HasLocalCovInputs p` holds for `p ≥ 5`.
-/

@[expose] public section

namespace BSDTamagawa.CovarianceDecay

/-! ### Two elementary estimates -/

/-- **`n³ ≤ 4 · 2^n` for `n ≥ 5`.** -/
theorem cube_le_four_mul_two_pow {n : ℕ} (hn : 5 ≤ n) : n ^ 3 ≤ 4 * 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 3 * n ^ 2 + 3 * n + 1 ≤ n ^ 3 := by nlinarith
    calc (n + 1) ^ 3 = n ^ 3 + (3 * n ^ 2 + 3 * n + 1) := by ring
      _ ≤ n ^ 3 + n ^ 3 := by omega
      _ = 2 * n ^ 3 := by ring
      _ ≤ 2 * (4 * 2 ^ n) := by omega
      _ = 4 * 2 ^ (n + 1) := by ring

/-- **`∑_{s ≥ 0} (s + m) x^s ≤ 2 + 2m` for `0 ≤ x ≤ 1/2`.** -/
theorem tsum_add_mul_geometric_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (m : ℕ) :
    ∑' s : ℕ, ((s : ℝ) + m) * x ^ s ≤ 2 + 2 * m := by
  have hx1 : x < 1 := by linarith
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hnorm : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; linarith
  have hs1 : Summable fun s : ℕ => (s : ℝ) * x ^ s := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  have hs2 : Summable fun s : ℕ => (m : ℝ) * x ^ s :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left _
  have hsplit : (∑' s : ℕ, ((s : ℝ) + m) * x ^ s)
      = (∑' s : ℕ, (s : ℝ) * x ^ s) + ∑' s : ℕ, (m : ℝ) * x ^ s := by
    rw [← hs1.tsum_add hs2]
    exact tsum_congr fun s => by ring
  have e1 : (∑' s : ℕ, (s : ℝ) * x ^ s) = x / (1 - x) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have e2 : (∑' s : ℕ, (m : ℝ) * x ^ s) = (m : ℝ) * (1 - x)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 hx1]
  have hinv : (1 - x)⁻¹ ≤ 2 := by
    calc (1 - x)⁻¹ = 1 / (1 - x) := (one_div _).symm
      _ ≤ 2 := by rw [div_le_iff₀ hpos]; linarith
  have b1 : x / (1 - x) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have b2 : (m : ℝ) * (1 - x)⁻¹ ≤ 2 * m := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  rw [hsplit, e1, e2]
  linarith

end BSDTamagawa.CovarianceDecay

namespace WeierstrassCurve

open scoped ENNReal
open BSDTamagawa.CovarianceDecay

variable {p : ℕ} [Fact p.Prime]

/-! ### The `ℝ`-valued forms of the pointwise bound and the tail law of `δ_p` -/

/-- `(δ_p(t)).toReal ≤ 9/p²` for every `t ≠ 1` and every prime `p`. -/
theorem toReal_δ_le_nine_div_sq {t : ℕ} (ht : t ≠ 1) : (δ p t).toReal ≤ 9 / (p : ℝ) ^ 2 := by
  have hp0 : ((p : ℝ≥0∞)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hne : (9 : ℝ≥0∞) / (p : ℝ≥0∞) ^ 2 ≠ ⊤ := (ENNReal.div_lt_top (by norm_num) hp0).ne
  have h := ENNReal.toReal_mono hne (δ_le_nine_div_sq (p := p) ht)
  rwa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, show
    ((9 : ℝ≥0∞)).toReal = (9 : ℝ) from by norm_num] at h

/-- **The geometric tail law in `ℝ`.** For `t ≥ 5`, `(δ_p(t)).toReal = α_p (p^{-1})^t`. -/
theorem toReal_δ_of_geom {a : ℝ≥0∞}
    (hgeom : ∀ t : ℕ, 5 ≤ t → δ p t = a * ((p : ℝ≥0∞)⁻¹) ^ t) {t : ℕ} (ht : 5 ≤ t) :
    (δ p t).toReal = a.toReal * ((p : ℝ)⁻¹) ^ t := by
  rw [hgeom t ht, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

/-- `p^{-1} ≤ 1/2` for a prime `p`. -/
theorem inv_cast_prime_le_half : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
  have h := two_le_cast_prime (p := p)
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  simpa using h

/-! ### `v_r` against the range of `t` -/

/-- `v_r(t) ≤ max 1 t` for a prime `r`. -/
theorem padicValNat_le_max_one {r : ℕ} (hr : r.Prime) (t : ℕ) : padicValNat r t ≤ max 1 t :=
  le_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self (two_pow_padicValNat_le hr t))

/-- `v_r(t) ≤ 2` for `t ≤ 4` and a prime `r`. -/
theorem padicValNat_le_two_of_le_four {r : ℕ} (hr : r.Prime) {t : ℕ} (ht : t ≤ 4) :
    padicValNat r t ≤ 2 := by
  have h := two_pow_padicValNat_le hr t
  have h4 : max 1 t ≤ 4 := by omega
  by_contra hcon
  have h3 : 3 ≤ padicValNat r t := by omega
  have h8 : 2 ^ 3 ≤ 2 ^ padicValNat r t := Nat.pow_le_pow_right (by norm_num) h3
  omega

/-- `valuationTerm p r t = 0` for `t < r`. -/
theorem valuationTerm_eq_zero_of_lt {r : ℕ} {t : ℕ} (ht : t < r) :
    valuationTerm p r t = 0 := by
  have hv : padicValNat r t = 0 := by
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · exact padicValNat_zero_right r
    · exact padicValNat.eq_zero_of_not_dvd fun hd => by
        have := Nat.le_of_dvd ht0 hd
        omega
  rw [valuationTerm, hv, Nat.cast_zero, mul_zero]

/-! ### The two marginal moment bounds

Here `μ_{p,r} = ∑'_t (δ_p(t)).toReal v_r(t)`. -/

/-- **`μ_{p,r} ≤ 56 p^{-2}` for every prime `r` and every prime `p`** satisfying the geometric tail
law. -/
theorem valuationMoment_le_fiftysix (h : HasTailGeometricLaw p) {r : ℕ} (hr : r.Prime) :
    valuationMoment p r ≤ 56 * ((p : ℝ)⁻¹) ^ 2 := by
  obtain ⟨a, ha, hgeom⟩ := h
  have hs : Summable (valuationTerm p r) :=
    summable_valuationTerm_of_tailLaw ⟨a, ha, hgeom⟩ hr
  set x : ℝ := ((p : ℝ))⁻¹ with hxdef
  have hx0 : (0 : ℝ) ≤ x := by rw [hxdef]; positivity
  have hx : x ≤ 1 / 2 := inv_cast_prime_le_half
  have haR : a.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top ha
    simpa using this
  have haR0 : (0 : ℝ) ≤ a.toReal := ENNReal.toReal_nonneg
  have hf0 : valuationTerm p r 0 = 0 := by
    rw [valuationTerm, padicValNat_zero_right, Nat.cast_zero, mul_zero]
  have hf1 : valuationTerm p r 1 = 0 := by
    rw [valuationTerm, padicValNat_one_right, Nat.cast_zero, mul_zero]
  have hfk : ∀ t : ℕ, t ≠ 1 → t ≤ 4 → valuationTerm p r t ≤ 18 * x ^ 2 := by
    intro t ht ht4
    have h1 : (δ p t).toReal ≤ 9 * x ^ 2 := by
      have := toReal_δ_le_nine_div_sq (p := p) ht
      rw [hxdef, inv_pow]
      rw [div_eq_mul_inv] at this
      linarith
    have h2 : ((padicValNat r t : ℕ) : ℝ) ≤ 2 := by
      exact_mod_cast padicValNat_le_two_of_le_four hr ht4
    have := mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
    rw [valuationTerm]
    linarith
  have hhead : ∑ t ∈ Finset.range 5, valuationTerm p r t ≤ 54 * x ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one, hf0, hf1]
    have h2 := hfk 2 (by norm_num) (by norm_num)
    have h3 := hfk 3 (by norm_num) (by norm_num)
    have h4 := hfk 4 (by norm_num) (by norm_num)
    linarith
  have hst : Summable fun s : ℕ => valuationTerm p r (s + 5) := (summable_nat_add_iff 5).2 hs
  have hdomsum : Summable fun s : ℕ => x ^ 5 * (((s : ℝ) + 5) * x ^ s) := by
    refine Summable.mul_left _ ?_
    have hnorm : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; linarith
    have h1 : Summable fun s : ℕ => (s : ℝ) * x ^ s := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    have h2 : Summable fun s : ℕ => (5 : ℝ) * x ^ s :=
      (summable_geometric_of_lt_one hx0 (by linarith)).mul_left _
    exact (h1.add h2).congr fun s => by ring
  have hterm : ∀ s : ℕ, valuationTerm p r (s + 5) ≤ x ^ 5 * (((s : ℝ) + 5) * x ^ s) := by
    intro s
    have hv : ((padicValNat r (s + 5) : ℕ) : ℝ) ≤ (s : ℝ) + 5 := by
      have h := padicValNat_le_max_one hr (s + 5)
      exact_mod_cast (show padicValNat r (s + 5) ≤ s + 5 by omega)
    have hxs : (0 : ℝ) ≤ x ^ (s + 5) := by positivity
    have hstep : a.toReal * x ^ (s + 5) ≤ x ^ (s + 5) := by nlinarith
    rw [valuationTerm, toReal_δ_of_geom hgeom (by omega)]
    calc a.toReal * x ^ (s + 5) * ((padicValNat r (s + 5) : ℕ) : ℝ)
        ≤ x ^ (s + 5) * ((s : ℝ) + 5) :=
          mul_le_mul hstep hv (Nat.cast_nonneg _) hxs
      _ = x ^ 5 * (((s : ℝ) + 5) * x ^ s) := by rw [pow_add]; ring
  have htail : (∑' s : ℕ, valuationTerm p r (s + 5)) ≤ 12 * x ^ 5 := by
    refine (hst.tsum_le_tsum hterm hdomsum).trans ?_
    rw [tsum_mul_left]
    have hgeo : (∑' s : ℕ, ((s : ℝ) + 5) * x ^ s) ≤ 12 := by
      have h := tsum_add_mul_geometric_le hx0 hx 5
      norm_num at h
      exact h
    linarith [mul_le_mul_of_nonneg_left hgeo (by positivity : (0 : ℝ) ≤ x ^ 5)]
  have hsplit := hs.sum_add_tsum_nat_add 5
  have hx3 : x ^ 3 ≤ 1 / 8 := by
    have h := pow_le_pow_left₀ hx0 hx 3
    norm_num at h
    exact h
  have hprod : x ^ 3 * x ^ 2 ≤ 1 / 8 * x ^ 2 :=
    mul_le_mul_of_nonneg_right hx3 (by positivity)
  have hcube : 12 * x ^ 5 ≤ 2 * x ^ 2 := by nlinarith [hprod]
  rw [valuationMoment, ← hsplit]
  linarith

/-- **`μ_{p,r} ≤ (2r + 2) p^{-r}` for a prime `r ≥ 5` and every prime `p`** satisfying the
geometric tail law. -/
theorem valuationMoment_le_sharp (h : HasTailGeometricLaw p) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) :
    valuationMoment p r ≤ (2 * (r : ℝ) + 2) * ((p : ℝ)⁻¹) ^ r := by
  obtain ⟨a, ha, hgeom⟩ := h
  have hs : Summable (valuationTerm p r) :=
    summable_valuationTerm_of_tailLaw ⟨a, ha, hgeom⟩ hr
  set x : ℝ := ((p : ℝ))⁻¹ with hxdef
  have hx0 : (0 : ℝ) ≤ x := by rw [hxdef]; positivity
  have hx : x ≤ 1 / 2 := inv_cast_prime_le_half
  have haR : a.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top ha
    simpa using this
  have hsupp : Function.support (valuationTerm p r) ⊆ Set.range fun s : ℕ => s + r := by
    intro t ht
    have hrt : r ≤ t := by
      by_contra hc
      exact ht (valuationTerm_eq_zero_of_lt (by omega))
    exact ⟨t - r, Nat.sub_add_cancel hrt⟩
  have hshift : (∑' s : ℕ, valuationTerm p r (s + r)) = valuationMoment p r :=
    Function.Injective.tsum_eq (fun u v huv => by simpa using huv) hsupp
  have hst : Summable fun s : ℕ => valuationTerm p r (s + r) := (summable_nat_add_iff r).2 hs
  have hdomsum : Summable fun s : ℕ => x ^ r * (((s : ℝ) + r) * x ^ s) := by
    refine Summable.mul_left _ ?_
    have hnorm : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; linarith
    have h1 : Summable fun s : ℕ => (s : ℝ) * x ^ s := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    have h2 : Summable fun s : ℕ => (r : ℝ) * x ^ s :=
      (summable_geometric_of_lt_one hx0 (by linarith)).mul_left _
    exact (h1.add h2).congr fun s => by ring
  have hterm : ∀ s : ℕ, valuationTerm p r (s + r) ≤ x ^ r * (((s : ℝ) + r) * x ^ s) := by
    intro s
    have hv : ((padicValNat r (s + r) : ℕ) : ℝ) ≤ (s : ℝ) + r := by
      have h := padicValNat_le_max_one hr (s + r)
      exact_mod_cast (show padicValNat r (s + r) ≤ s + r by omega)
    have hxs : (0 : ℝ) ≤ x ^ (s + r) := by positivity
    have hstep : a.toReal * x ^ (s + r) ≤ x ^ (s + r) := by nlinarith
    rw [valuationTerm, toReal_δ_of_geom hgeom (by omega)]
    calc a.toReal * x ^ (s + r) * ((padicValNat r (s + r) : ℕ) : ℝ)
        ≤ x ^ (s + r) * ((s : ℝ) + r) :=
          mul_le_mul hstep hv (Nat.cast_nonneg _) hxs
      _ = x ^ r * (((s : ℝ) + r) * x ^ s) := by rw [pow_add]; ring
  rw [← hshift]
  refine (hst.tsum_le_tsum hterm hdomsum).trans ?_
  rw [tsum_mul_left]
  have hgeo : (∑' s : ℕ, ((s : ℝ) + r) * x ^ s) ≤ 2 * (r : ℝ) + 2 := by
    have h := tsum_add_mul_geometric_le hx0 hx r
    linarith
  linarith [mul_le_mul_of_nonneg_left hgeo (by positivity : (0 : ℝ) ≤ x ^ r)]

/-! ### One `r`-indexed bound, and its `r^{-2}` decay -/

/-- The `r`-dependent factor `B(r)` of the marginal bound `μ_{p,r} ≤ B(r) p^{-2}`: `4(2r+2)2^{-r}`
for `r ≥ 5`, and `56` otherwise. -/
noncomputable def momentDecay (r : ℕ) : ℝ :=
  if 5 ≤ r then 4 * (2 * (r : ℝ) + 2) * (1 / 2 : ℝ) ^ r else 56

/-- `0 ≤ B(r)`. -/
theorem momentDecay_nonneg (r : ℕ) : 0 ≤ momentDecay r := by
  rw [momentDecay]
  split_ifs with h
  · positivity
  · norm_num

/-- **`μ_{p,r} ≤ B(r) p^{-2}` for every prime `r` and every prime `p`** satisfying the geometric
tail law. -/
theorem valuationMoment_le_momentDecay (h : HasTailGeometricLaw p) {r : ℕ} (hr : r.Prime) :
    valuationMoment p r ≤ momentDecay r * ((p : ℝ)⁻¹) ^ 2 := by
  rw [momentDecay]
  split_ifs with hr5
  · refine (valuationMoment_le_sharp h hr hr5).trans ?_
    set x : ℝ := ((p : ℝ))⁻¹ with hxdef
    have hx0 : (0 : ℝ) ≤ x := by rw [hxdef]; positivity
    have hx : x ≤ 1 / 2 := inv_cast_prime_le_half
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    have hk : x ^ k ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ hx0 hx k
    calc (2 * ((k + 2 : ℕ) : ℝ) + 2) * x ^ (k + 2)
        = (2 * ((k + 2 : ℕ) : ℝ) + 2) * (x ^ k * x ^ 2) := by rw [pow_add]
      _ ≤ (2 * ((k + 2 : ℕ) : ℝ) + 2) * ((1 / 2 : ℝ) ^ k * x ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk (by positivity))
            (by push_cast; positivity)
      _ = 4 * (2 * ((k + 2 : ℕ) : ℝ) + 2) * (1 / 2 : ℝ) ^ (k + 2) * x ^ 2 := by
          rw [pow_add]; ring
  · exact valuationMoment_le_fiftysix h hr

/-- **`B(r) r² ≤ 504` at every prime `r`**, with equality at `r = 3`. -/
theorem momentDecay_mul_sq_le {r : ℕ} (hr : r.Prime) : momentDecay r * (r : ℝ) ^ 2 ≤ 504 := by
  rw [momentDecay]
  split_ifs with hr5
  · have hcube : (r : ℝ) ^ 3 ≤ 4 * 2 ^ r := by
      have h := cube_le_four_mul_two_pow hr5
      calc (r : ℝ) ^ 3 = ((r ^ 3 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((4 * 2 ^ r : ℕ) : ℝ) := by exact_mod_cast h
        _ = 4 * 2 ^ r := by push_cast; ring
    have hy : ((1 : ℝ) / 2) ^ r = ((2 : ℝ) ^ r)⁻¹ := by
      rw [one_div, inv_pow]
    have h2r : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
    have hkey : (r : ℝ) ^ 3 * ((2 : ℝ) ^ r)⁻¹ ≤ 4 := by
      rw [mul_inv_le_iff₀ h2r]
      linarith
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
      have h : (1 : ℕ) ≤ r := by omega
      exact_mod_cast h
    have hinv0 : (0 : ℝ) ≤ ((2 : ℝ) ^ r)⁻¹ := by positivity
    have hsq : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := by nlinarith
    have hstep : (r : ℝ) ^ 2 * ((2 : ℝ) ^ r)⁻¹ ≤ (r : ℝ) ^ 3 * ((2 : ℝ) ^ r)⁻¹ :=
      mul_le_mul_of_nonneg_right hsq hinv0
    rw [hy]
    nlinarith [hkey, hstep]
  · have h3 : (r : ℝ) ≤ 3 := by
      rcases prime_eq_two_or_eq_three_or_five_le hr with rfl | rfl | h
      · norm_num
      · norm_num
      · omega
    have h0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    nlinarith

/-! ### `|C_p(ℓ, ℓ')| ≤ μ_{p,ℓ} μ_{p,ℓ'}` -/

section Pair

variable {ℓ ℓ' : ℕ}

/-- **`|C_p(ℓ, ℓ')| ≤ μ_{p,ℓ} μ_{p,ℓ'}`**, assuming `HasLocalCovInputs p`, for distinct primes
`ℓ ≠ ℓ'`. -/
theorem abs_localCov_le_valuationMoment_mul (hin : HasLocalCovInputs p) (hℓ : ℓ.Prime)
    (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    |localCov p ℓ ℓ'| ≤ valuationMoment p ℓ * valuationMoment p ℓ' := by
  have hneg : localCov p ℓ ℓ' < 0 := localCov_neg_of_inputs hin hℓ hℓ' hne
  have hc : 0 ≤ crossValuationMoment p ℓ ℓ' := crossValuationMoment_nonneg ℓ ℓ'
  have hm : 0 ≤ valuationMoment p ℓ * valuationMoment p ℓ' :=
    mul_nonneg (valuationMoment_nonneg ℓ) (valuationMoment_nonneg ℓ')
  have hexp : localCov p ℓ ℓ' = crossValuationMoment p ℓ ℓ'
      - valuationMoment p ℓ * valuationMoment p ℓ' := rfl
  rw [abs_le]
  refine ⟨?_, by linarith⟩
  rw [hexp]
  linarith

end Pair

/-! ### The sum over the primes -/

/-- `∑_{p ∈ 𝒫} p^{-2}` converges. -/
theorem summable_primeInvSq : Summable fun q : {n : ℕ // n.Prime} => 1 / ((q : ℕ) : ℝ) ^ 2 :=
  ((Real.summable_one_div_nat_pow.2 (by norm_num)).comp_injective
    (Subtype.val_injective (p := fun n : ℕ => n.Prime)))

/-- The sum `∑_{p ∈ 𝒫} p^{-2}`. -/
noncomputable def primeInvSqSum : ℝ := ∑' q : {n : ℕ // n.Prime}, 1 / ((q : ℕ) : ℝ) ^ 2

/-- `0 ≤ ∑_{p ∈ 𝒫} p^{-2}`. -/
theorem primeInvSqSum_nonneg : 0 ≤ primeInvSqSum :=
  tsum_nonneg fun q => by positivity

/-! ### The local covariance inputs at every prime `p ≥ 5` -/

/-- **`HasTailConstantLaw p` holds for every prime `p ≥ 5`**: `δ_p(t) = α_p p^{-t}` for `t ≥ 5`,
with `1/88572 ≤ α_p < 1/2`. -/
theorem hasTailConstantLaw_of_five_le (hp : 5 ≤ p) : HasTailConstantLaw p := by
  have hs : StratScaleInvariant p := stratScaleInvariant_of_five_le hp
  obtain ⟨hlt, hge⟩ := α_bounds_of_stratScaleInvariant hp hs
  rw [α_eq_tailConstant_of_stratScaleInvariant hp hs] at hlt hge
  exact ⟨tailConstant p, fun _ ht => δ_eq_tailConstant_mul hp hs ht, hlt, hge,
    fun h => absurd hp (by omega), fun h => absurd hp (by omega)⟩

/-- **`HasLocalCovInputs p` holds for every prime `p ≥ 5`.** -/
theorem hasLocalCovInputs_of_five_le (hp : 5 ≤ p) : HasLocalCovInputs p :=
  ⟨hasTailConstantLaw_of_five_le hp, inv_two_mul_sq_le_headSum_two hp,
    inv_three_mul_cube_le_headSum_three hp⟩

end WeierstrassCurve
