/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Moments.DirichletSpecialization

/-!
# Absolute convergence of the Tamagawa Euler product at every `s : ℂ`

Let `L_p(s) = ∑_{t ≥ 1} δ_p(t) t^{-s}` be the local Euler factor of the limiting Tamagawa law. For
every `s : ℂ`, with no restriction on `Re(s)`, `∑_{p ∈ 𝒫} ‖L_p(s) - 1‖ < ∞`. Consequently the
family `(L_p(s))_p` is multipliable at every `s`, and the predicate `HasEulerProductAt s`, whose
antecedent is exactly this summability, is equivalent to its conclusion.

## Main results

* `WeierstrassCurve.summable_norm_tamagawaEulerFactor_sub_one`: `∑_{p ∈ 𝒫} ‖L_p(s) - 1‖ < ∞` for
  every `s : ℂ`.
* `WeierstrassCurve.multipliable_tamagawaEulerFactor`: the local factors are multipliable at every
  `s : ℂ`.
* `WeierstrassCurve.hasEulerProductAt_iff`, `WeierstrassCurve.hasEulerProductOffHalfPlane_iff`:
  `HasEulerProductAt s` is equivalent to the absolute convergence of `∑_m P_Tam(m) m^{-s}` together
  with `∑_m P_Tam(m) m^{-s} = ∏_{p ∈ 𝒫} L_p(s)`.
* `WeierstrassCurve.summable_norm_tamagawaDensity_mul_cpow_iff`: `∑_m ‖P_Tam(m) m^{-s}‖ < ∞` if and
  only if `∑_m P_Tam(m) m^{-Re(s)} < ∞`.

## Implementation notes

At a prime `p ≥ 5`, where the geometric tail law holds, and for any real `y ≥ max(1, 1 - Re(s))`,
`‖L_p(s) - 1‖ ≤ 2 ‖G_p(y) - 1‖ ≤ 2 · momentBoundConst ⌈y⌉₊ / p²`, the first inequality following
termwise from `‖t^{-s} - 1‖ ≤ 2 (t^y - 1)` and `∑_t δ_p(t) = 1`. The primes `2` and `3` do not
affect summability. Since `L_p(s)` is an unconditional `tsum`, it takes the value `0` where the
local series diverges, so the summability over `p` carries no information about any single prime.
-/

@[expose] public section

namespace WeierstrassCurve

/-! ### Two elementary bounds on the Dirichlet weight -/

/-- `1 ≤ t^y` for natural `t ≥ 1` and real `y ≥ 0`. -/
lemma one_le_natCast_rpow {t : ℕ} (ht : 1 ≤ t) {y : ℝ} (hy : 0 ≤ y) : (1 : ℝ) ≤ (t : ℝ) ^ y :=
  Real.one_le_rpow (by exact_mod_cast ht) hy

/-- For `t ≥ 1` and any real `y` with `y ≥ 1` and `y ≥ 1 - Re(s)`,

`‖t^{-s} - 1‖ ≤ 2 (t^y - 1)`. -/
lemma norm_natCast_cpow_neg_sub_one_le {t : ℕ} (ht : 1 ≤ t) {s : ℂ} {y : ℝ} (hy1 : 1 ≤ y)
    (hys : -s.re + 1 ≤ y) : ‖(t : ℂ) ^ (-s) - 1‖ ≤ 2 * ((t : ℝ) ^ y - 1) := by
  by_cases ht1 : t = 1
  · subst ht1
    simp
  have ht2R : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 2 ≤ t by omega)
  have htpos : (0 : ℝ) < (t : ℝ) := by linarith
  have hA1 : (1 : ℝ) ≤ (t : ℝ) ^ (y - 1) := one_le_natCast_rpow ht (by linarith)
  have hsplit : (t : ℝ) ^ y = (t : ℝ) ^ (y - 1) * (t : ℝ) := by
    rw [← Real.rpow_add_one htpos.ne' (y - 1)]
    norm_num
  have hle : (t : ℝ) ^ (-s.re) ≤ (t : ℝ) ^ (y - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc ‖(t : ℂ) ^ (-s) - 1‖ ≤ ‖(t : ℂ) ^ (-s)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = (t : ℝ) ^ (-s.re) + 1 := by
        rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < t), Complex.neg_re, norm_one]
    _ ≤ 2 * ((t : ℝ) ^ y - 1) := by
        rw [hsplit]
        nlinarith [mul_le_mul_of_nonneg_left ht2R (by linarith : (0 : ℝ) ≤ (t : ℝ) ^ (y - 1))]

/-! ### The local deviation bound at a complex exponent -/

/-- Under the geometric tail law, `∑_t δ_p(t) t^{-s}` converges whenever `-Re(s) ≤ y` for some
real `y`, being dominated by the real series `∑_t δ_p(t) t^y`. -/
lemma summable_δ_toReal_mul_cpow_of_tailLaw (p : ℕ) [Fact p.Prime]
    (h : HasTailGeometricLaw p) {s : ℂ} {y : ℝ} (hys : -s.re ≤ y) :
    Summable fun t : ℕ => ((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => ?_)
    (summable_δ_toReal_mul_rpow_of_tailLaw p h y))
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [δ_zero]
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg,
      Complex.norm_natCast_cpow_of_pos ht, Complex.neg_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast ht) hys) ENNReal.toReal_nonneg

/-- Under the geometric tail law, `1 ≤ ∑_t δ_p(t) t^y` for every `y ≥ 0`. -/
lemma one_le_tsum_δ_toReal_mul_rpow_of_tailLaw (p : ℕ) [Fact p.Prime]
    (h : HasTailGeometricLaw p) {y : ℝ} (hy : 0 ≤ y) :
    (1 : ℝ) ≤ ∑' t : ℕ, (δ p t).toReal * (t : ℝ) ^ y := by
  rw [← tsum_δ_toReal p]
  refine Summable.tsum_le_tsum (fun t => ?_) (summable_δ_toReal p)
    (summable_δ_toReal_mul_rpow_of_tailLaw p h y)
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [δ_zero]
  · exact le_mul_of_one_le_right ENNReal.toReal_nonneg (one_le_natCast_rpow ht hy)

/-- For a prime `p` at which the geometric tail law holds, and any real `y` with `y ≥ 1` and
`y ≥ 1 - Re(s)`,

`‖(∑_{t ≥ 1} δ_p(t) t^{-s}) - 1‖ ≤ 2 ‖G_p(y) - 1‖`,

where `G_p(y)` is the local moment factor `momentLocalFactor p y`. -/
lemma norm_tsum_δ_toReal_mul_cpow_neg_sub_one_le_of_tailLaw (p : ℕ) [Fact p.Prime]
    (h : HasTailGeometricLaw p) {s : ℂ} {y : ℝ} (hy1 : 1 ≤ y) (hys : -s.re + 1 ≤ y) :
    ‖(∑' t : ℕ, ((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s)) - 1‖
      ≤ 2 * ‖momentLocalFactor p y - 1‖ := by
  have hd0 : ∀ t : ℕ, 0 ≤ (δ p t).toReal := fun _ => ENNReal.toReal_nonneg
  have hsd : Summable fun t : ℕ => (δ p t).toReal := summable_δ_toReal p
  have hsy : Summable fun t : ℕ => (δ p t).toReal * (t : ℝ) ^ y :=
    summable_δ_toReal_mul_rpow_of_tailLaw p h y
  have hone : ∑' t : ℕ, (δ p t).toReal = 1 := tsum_δ_toReal p
  have hsc := summable_δ_toReal_mul_cpow_of_tailLaw p h (s := s) (by linarith : -s.re ≤ y)
  have hterm : ∀ t : ℕ, ‖((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) - ((δ p t).toReal : ℂ)‖
      ≤ 2 * ((δ p t).toReal * ((t : ℝ) ^ y - 1)) := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [δ_zero]
    · rw [show ((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) - ((δ p t).toReal : ℂ)
          = ((δ p t).toReal : ℂ) * ((t : ℂ) ^ (-s) - 1) by ring,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg (hd0 t)]
      calc (δ p t).toReal * ‖(t : ℂ) ^ (-s) - 1‖
          ≤ (δ p t).toReal * (2 * ((t : ℝ) ^ y - 1)) :=
            mul_le_mul_of_nonneg_left (norm_natCast_cpow_neg_sub_one_le ht hy1 hys) (hd0 t)
        _ = 2 * ((δ p t).toReal * ((t : ℝ) ^ y - 1)) := by ring
  have hRsum : Summable fun t : ℕ => 2 * ((δ p t).toReal * ((t : ℝ) ^ y - 1)) :=
    ((hsy.sub hsd).mul_left 2).congr fun t => by ring
  have hNsum : Summable fun t : ℕ =>
      ‖((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) - ((δ p t).toReal : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hRsum
  have hgey := one_le_tsum_δ_toReal_mul_rpow_of_tailLaw p h (by linarith : 0 ≤ y)
  calc ‖(∑' t : ℕ, ((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s)) - 1‖
      = ‖∑' t : ℕ, (((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) - ((δ p t).toReal : ℂ))‖ := by
        rw [hsc.tsum_sub (Complex.summable_ofReal.mpr hsd), ← Complex.ofReal_tsum, hone,
          Complex.ofReal_one]
    _ ≤ ∑' t : ℕ, ‖((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) - ((δ p t).toReal : ℂ)‖ :=
        norm_tsum_le_tsum_norm hNsum
    _ ≤ ∑' t : ℕ, 2 * ((δ p t).toReal * ((t : ℝ) ^ y - 1)) :=
        Summable.tsum_le_tsum hterm hNsum hRsum
    _ = 2 * ((∑' t : ℕ, (δ p t).toReal * (t : ℝ) ^ y) - 1) := by
        have hcongr : ∑' t : ℕ, (δ p t).toReal * ((t : ℝ) ^ y - 1)
            = (∑' t : ℕ, (δ p t).toReal * (t : ℝ) ^ y) - ∑' t : ℕ, (δ p t).toReal := by
          rw [← hsy.tsum_sub hsd]
          exact tsum_congr fun t => by ring
        rw [tsum_mul_left, hcongr, hone]
    _ = 2 * ‖momentLocalFactor p y - 1‖ := by
        rw [momentLocalFactor_eq_ofReal, ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_of_nonneg (by linarith)]

/-- At a prime `p` at which the geometric tail law holds, for every `s : ℂ`,

`‖L_p(s) - 1‖ ≤ 2 · momentBoundConst ⌈|Re(s)| + 1⌉₊ / p²`. -/
lemma norm_tamagawaEulerFactor_sub_one_le_of_tailLaw (p : ℕ) [Fact p.Prime]
    (h : HasTailGeometricLaw p) (hp : p.Prime) (s : ℂ) :
    ‖tamagawaEulerFactor ⟨p, hp⟩ s - 1‖
      ≤ 2 * momentBoundConst ⌈|s.re| + 1⌉₊ / (p : ℝ) ^ 2 := by
  have hy1 : (1 : ℝ) ≤ |s.re| + 1 := by linarith [abs_nonneg s.re]
  have hys : -s.re + 1 ≤ |s.re| + 1 := by linarith [neg_abs_le s.re]
  rw [tamagawaEulerFactor_def]
  refine (norm_tsum_δ_toReal_mul_cpow_neg_sub_one_le_of_tailLaw p h hy1 hys).trans ?_
  have hk := norm_momentLocalFactor_sub_one_le_of_tailLaw p h ⌈|s.re| + 1⌉₊
    (Nat.le_ceil (|s.re| + 1))
  calc 2 * ‖momentLocalFactor p (|s.re| + 1) - 1‖
      ≤ 2 * (momentBoundConst ⌈|s.re| + 1⌉₊ / (p : ℝ) ^ 2) := by linarith
    _ = 2 * momentBoundConst ⌈|s.re| + 1⌉₊ / (p : ℝ) ^ 2 := by ring

/-! ### Summability of the local deviations at every complex exponent -/

/-- For every `s : ℂ`, with no restriction on `Re(s)`,

`∑_{p ∈ 𝒫} ‖(∑_{t ≥ 1} δ_p(t) t^{-s}) - 1‖ < ∞`. -/
theorem summable_norm_tamagawaEulerFactor_sub_one (s : ℂ) :
    Summable fun p : {q : ℕ // q.Prime} => ‖tamagawaEulerFactor p s - 1‖ := by
  classical
  have hC : (0 : ℝ) ≤ 2 * momentBoundConst ⌈|s.re| + 1⌉₊ := by
    have := momentBoundConst_pos ⌈|s.re| + 1⌉₊
    linarith
  have key : Summable fun n : ℕ =>
      if h : n.Prime then ‖tamagawaEulerFactor ⟨n, h⟩ s - 1‖ else 0 := by
    refine (summable_nat_add_iff 5).mp (Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      ((summable_nat_add_iff 5).mpr
        (summable_const_div_sq (2 * momentBoundConst ⌈|s.re| + 1⌉₊))))
    · by_cases hq : (n + 5).Prime
      · rw [dite_eq_left hq]
        exact norm_nonneg _
      · rw [dite_eq_right hq]
    · by_cases hq : (n + 5).Prime
      · have : Fact (n + 5).Prime := ⟨hq⟩
        rw [dite_eq_left hq]
        exact norm_tamagawaEulerFactor_sub_one_le_of_tailLaw (n + 5)
          (hasTailGeometricLaw_of_stratScaleInvariant (by omega)
            (stratScaleInvariant_of_five_le (by omega))) hq s
      · rw [dite_eq_right hq]
        positivity
  refine (key.subtype Nat.Prime).congr fun p => ?_
  simp only [Function.comp_apply]
  rw [dite_eq_left p.2]

/-- For every `s : ℂ`, the family of local Euler factors `(L_p(s))_{p ∈ 𝒫}` is multipliable. -/
theorem multipliable_tamagawaEulerFactor (s : ℂ) :
    Multipliable fun p : {q : ℕ // q.Prime} => tamagawaEulerFactor p s :=
  (multipliable_one_add_of_summable
    (f := fun p : {q : ℕ // q.Prime} => tamagawaEulerFactor p s - 1)
    (summable_norm_tamagawaEulerFactor_sub_one s)).congr fun _ => by ring

/-- For every `s : ℂ`, `HasEulerProductAt s` holds if and only if the Dirichlet series
`∑_m P_Tam(m) m^{-s}` converges absolutely and equals `∏_{p ∈ 𝒫} L_p(s)`. -/
theorem hasEulerProductAt_iff (s : ℂ) :
    HasEulerProductAt s ↔
      (Summable fun m : ℕ => ‖(tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)‖) ∧
        ∑' m : ℕ, (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)
          = ∏' p : {q : ℕ // q.Prime}, tamagawaEulerFactor p s :=
  ⟨fun h => h (summable_norm_tamagawaEulerFactor_sub_one s), fun h _ => h⟩

/-- For every `s : ℂ`,

`(∑_m ‖P_Tam(m) m^{-s}‖ < ∞) ↔ (∑_m P_Tam(m) m^{-Re(s)} < ∞)`. -/
theorem summable_norm_tamagawaDensity_mul_cpow_iff (s : ℂ) :
    (Summable fun m : ℕ => ‖(tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)‖) ↔
      Summable fun m : ℕ => tamagawaDensity m * (m : ℝ) ^ (-s.re) := by
  refine summable_congr fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [tamagawaDensity_zero]
    simp
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (tamagawaDensity_nonneg m),
      Complex.norm_natCast_cpow_of_pos hm, Complex.neg_re]

/-- `HasEulerProductOffHalfPlane` holds if and only if, for every `s : ℂ`, the Dirichlet series
`∑_{m ≥ 1} P_Tam(m) m^{-s}` converges absolutely and equals `∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{-s})`.
-/
theorem hasEulerProductOffHalfPlane_iff :
    HasEulerProductOffHalfPlane ↔ ∀ s : ℂ,
      (Summable fun m : ℕ => ‖(tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)‖) ∧
        ∑' m : ℕ, (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)
          = ∏' p : {q : ℕ // q.Prime}, tamagawaEulerFactor p s :=
  forall_congr' hasEulerProductAt_iff

end WeierstrassCurve
