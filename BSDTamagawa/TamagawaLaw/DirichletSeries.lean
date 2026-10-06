/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.TamagawaLaw.LimitingDensityExists
public import BSDTamagawa.GeneratingFunction.ScalarContinuity
public import BSDTamagawa.GeneratingFunction.ScalarSpecialization

/-!
# The Tamagawa Dirichlet series on `Re(s) ≥ 0`

For every `s ∈ ℂ` with `Re(s) ≥ 0`, the Dirichlet series of the limiting Tamagawa densities
converges absolutely and has an Euler product:

`∑_{m ≥ 1} P_Tam(m) m^{-s} = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{-s})`,

where `P_Tam(m)` is the limiting density `tamagawaDensity m` and `δ_p(t)` is the local density of
the Tamagawa number at `p`. Along the way the truncated proportions `P_Tam(m; X)` are shown to form
a tight family of probability vectors, the limiting densities to have total mass `1`, and
`P_Tam(·; X) → P_Tam` in `L¹`.

## Main results

* `WeierstrassCurve.summable_norm_tamagawaDensity_mul_cpow`: absolute convergence of the Dirichlet
  series on the half-plane `Re(s) ≥ 0`.
* `WeierstrassCurve.tsum_tamagawaDensity_mul_cpow`: the Euler product identity there.
* `WeierstrassCurve.tendsto_tsum_tamagawaProportion_mul_cpow`:
  `lim_{X → ∞} ∑_m P_Tam(m; X) m^{-s} = ∏_{p ∈ 𝒫} (∑_t δ_p(t) t^{-s})` for `Re(s) ≥ 0`.
* `WeierstrassCurve.exists_tsum_tamagawaProportion_add_le`: tightness, for every `ε > 0` there is
  `M` with `∑_{m ≥ M} P_Tam(m; X) ≤ ε` for all large `X`.
* `WeierstrassCurve.tsum_tamagawaDensity_eq_one_of_tendsto`: given convergence of each
  `P_Tam(m; X)`, the limiting densities have total mass `1`.
* `WeierstrassCurve.tendsto_tsum_abs_sub_of_tendsto`: given the same convergence,
  `∑_m |P_Tam(m; X) - P_Tam(m)| → 0`.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.MultiIndex
open BSDTamagawa.FiberCount BSDTamagawa.DegeneratePoint

/-! ### The scalar face `Π = ∅`, `w = 1` is the Dirichlet face -/

/-- At `Π = ∅` and `w = 1` the scalar weight `ψ_{s, w, 𝐳}(t) = w^{Ω(t)} 𝐳^{v(t)} t^{-s}` is the
Dirichlet weight `t^{-s}`, for every `t : ℕ`, `t = 0` included. -/
lemma scalarWeight_empty_one (s : ℂ) (z : (∅ : Finset ℕ) → ℂ) (t : ℕ) :
    scalarWeight ∅ s 1 z t = (t : ℂ) ^ (-s) := by
  rw [scalarWeight, one_pow, multiMonomial_of_isEmpty, one_mul, one_mul]

/-- At a prime `p`, the scalar local factor at `Π = ∅` and `w = 1` is
`h_p(s, 1, ()) = ∑_{t ≥ 1} δ_p(t) t^{-s}`, the sum being written over all of `ℕ` (the term at
`t = 0` vanishes). -/
lemma scalarLocalFactor_empty_one_of_prime (p : ℕ) [Fact p.Prime] (s : ℂ)
    (z : (∅ : Finset ℕ) → ℂ) :
    scalarLocalFactor ∅ p s 1 z = ∑' t : ℕ, ((δ p t).toReal : ℂ) * (t : ℂ) ^ (-s) := by
  rw [scalarLocalFactor_eq_tsum_of_prime]
  exact tsum_congr fun t => by rw [scalarWeight_empty_one]

/-! ### The Euler product at `s = 0` is `1` -/

/-- At a prime `p`, `h_p(0, 1, ()) = ∑_{t ≥ 1} δ_p(t) = 1`. -/
lemma scalarLocalFactor_empty_one_zero (p : ℕ) [Fact p.Prime] (z : (∅ : Finset ℕ) → ℂ) :
    scalarLocalFactor ∅ p 0 1 z = 1 := by
  have hne : ∀ t : ℕ, δ p t ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top (by rw [tsum_δ]; exact ENNReal.one_ne_top) (ENNReal.le_tsum t)
  have hreal : ∑' t : ℕ, (δ p t).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq hne, tsum_δ, ENNReal.toReal_one]
  rw [scalarLocalFactor_empty_one_of_prime,
    tsum_congr fun t : ℕ => by rw [neg_zero, Complex.cpow_zero, mul_one],
    ← Complex.ofReal_tsum, hreal, Complex.ofReal_one]

/-- The Euler product at `s = 0` is `∏'_p h_p(0, 1, ()) = 1`. -/
lemma tprod_scalarLocalFactor_empty_one_zero (z : (∅ : Finset ℕ) → ℂ) :
    ∏' p : ℕ, scalarLocalFactor ∅ p 0 1 z = 1 := by
  rw [tprod_congr fun p : ℕ => ?_, tprod_one]
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    exact scalarLocalFactor_empty_one_zero p z
  · exact scalarLocalFactor_of_not_prime hp 0 1 z

/-! ### The truncated proportions and the empirical average -/

/-- The numerator of `P_Tam(m; X)` is the fibre of `Tam` over `m` inside the height-truncated
family: `{E ∈ 𝓔(X) : Tam(E) = m} = {E : Ht ≤ X, Δ ≠ 0, Tam(E) = m}`. -/
theorem setOf_mem_and_tamagawaProduct_eq (m : ℕ) (X : ℝ) :
    {q : ℤ × ℤ | q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
        q ∈ integralShortNFFamily} ∧ tamagawaProduct q.1 q.2 = m} =
      {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
        q ∈ integralShortNFFamily ∧
        tamagawaProduct q.1 q.2 = m} :=
  Set.ext fun _ => by simp only [Set.mem_ofPred_eq, and_assoc]

open scoped Classical in
/-- For every `X ≥ 0`,

`(1/N(X)) ∑_{Ht(E) ≤ X} Tam(E)^{-s} = ∑_{m} P_Tam(m; X) m^{-s}`,

with `P_Tam(m; X)` the truncated proportion `tamagawaProportion m X`; when `N(X) = 0` both sides
are `0`. -/
theorem tsum_tamagawaProportion_mul_cpow (s : ℂ) (z : (∅ : Finset ℕ) → ℂ) {X : ℝ} (hX : 0 ≤ X) :
    ∑' m : ℕ, (tamagawaProportion m X : ℂ) * (m : ℂ) ^ (-s) =
      (∑' q : ℤ × ℤ, if (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily then
          scalarWeight ∅ s 1 z (tamagawaProduct q.1 q.2) else 0) /
        (integralShortNFCount X : ℂ) := by
  have hS := finite_setOf_height_le_and_mem_family hX
  have key := tsum_ncard_fiber_div_mul hS (fun q : ℤ × ℤ => tamagawaProduct q.1 q.2)
    (fun m : ℕ => (m : ℂ) ^ (-s)) (integralShortNFCount X : ℂ)
  have hcoeff : ∀ m : ℕ, ({q : ℤ × ℤ | q ∈ {q : ℤ × ℤ |
      (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily} ∧
      tamagawaProduct q.1 q.2 = m}.ncard : ℂ) / (integralShortNFCount X : ℂ) =
      (tamagawaProportion m X : ℂ) := by
    intro m
    rw [tamagawaProportion, ← setOf_mem_and_tamagawaProduct_eq m X]
    push_cast
    rfl
  refine Eq.trans (Eq.trans (tsum_congr fun m => ?_) key) ?_
  · rw [← hcoeff m]
  · congr 1
    refine tsum_congr fun q => ?_
    by_cases hq : q ∈ {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
        q ∈ integralShortNFFamily}
    · rw [Set.indicator_of_mem hq, ite_eq_left (show _ ∧ _ from hq), scalarWeight_empty_one]
    · rw [Set.indicator_of_notMem hq, ite_eq_right (show ¬(_ ∧ _) from hq)]

/-- For every `X ≥ 0`, only finitely many truncated proportions `P_Tam(m; X)` are nonzero. -/
theorem finite_setOf_tamagawaProportion_ne_zero {X : ℝ} (hX : 0 ≤ X) :
    {m : ℕ | tamagawaProportion m X ≠ 0}.Finite := by
  refine (finite_setOf_ncard_fiber_ne_zero (finite_setOf_height_le_and_mem_family hX)
    fun q : ℤ × ℤ => tamagawaProduct q.1 q.2).subset fun m hm => ?_
  rw [Set.mem_ofPred_eq, setOf_mem_and_tamagawaProduct_eq m X]
  exact fun h => hm (by rw [tamagawaProportion, h, Nat.cast_zero, zero_div])

/-- If `N(X) ≠ 0`, the truncated proportions have total mass `∑_m P_Tam(m; X) = 1`. -/
theorem tsum_tamagawaProportion_eq_one_of_count_ne_zero {X : ℝ}
    (hN : integralShortNFCount X ≠ 0) :
    ∑' m : ℕ, tamagawaProportion m X = 1 := by
  have hS : {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧
      q ∈ integralShortNFFamily}.Finite := Set.finite_of_ncard_ne_zero hN
  have hfib := tsum_ncard_fiber_div hS hN fun q : ℤ × ℤ => tamagawaProduct q.1 q.2
  rw [← hfib]
  exact tsum_congr fun m => by
    rw [tamagawaProportion, ← setOf_mem_and_tamagawaProduct_eq m X]; rfl

/-- For `X ≥ 4`, the truncated proportions have total mass `∑_m P_Tam(m; X) = 1`. -/
theorem tsum_tamagawaProportion_eq_one {X : ℝ} (hX : 4 ≤ X) :
    ∑' m : ℕ, tamagawaProportion m X = 1 :=
  tsum_tamagawaProportion_eq_one_of_count_ne_zero (integralShortNFCount_ne_zero_of_four_le hX)

/-! ### The limit of the truncated Dirichlet series -/

/-- For `Re(s) ≥ 0`,

`∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{-s}) = ∏'_{p : ℕ} h_p(s, 1, ())`. -/
lemma tprod_primes_tsum_δ_mul_cpow_eq {s : ℂ} (hs : 0 ≤ s.re) (z : (∅ : Finset ℕ) → ℂ) :
    ∏' p : {q : ℕ // q.Prime}, (∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * (t : ℂ) ^ (-s))
      = ∏' p : ℕ, scalarLocalFactor ∅ p s 1 z := by
  have hz1 : ∀ ℓ : (∅ : Finset ℕ), ‖z ℓ‖ ≤ 1 := fun ℓ => (Finset.notMem_empty _ ℓ.2).elim
  rw [← tprod_scalarLocalFactor_primes ∅ hs (by simp) hz1]
  refine tprod_congr fun p => ?_
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact (scalarLocalFactor_empty_one_of_prime (p : ℕ) s z).symm

/-- For every `s : ℂ` with `Re(s) ≥ 0`, the limit

`lim_{X → ∞} ∑_{m} P_Tam(m; X) m^{-s} = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{-s})`

exists and has the stated value. -/
theorem tendsto_tsum_tamagawaProportion_mul_cpow {s : ℂ} (hs : 0 ≤ s.re) :
    Tendsto (fun X : ℝ => ∑' m : ℕ, (tamagawaProportion m X : ℂ) * (m : ℂ) ^ (-s)) atTop
      (𝓝 (∏' p : {q : ℕ // q.Prime},
        ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * (t : ℂ) ^ (-s))) := by
  classical
  set z : (∅ : Finset ℕ) → ℂ := fun _ => 1 with hz
  have hz1 : ∀ ℓ : (∅ : Finset ℕ), ‖z ℓ‖ ≤ 1 := fun ℓ => (Finset.notMem_empty _ ℓ.2).elim
  have hx : ((s, (1 : ℂ), z) ∈ scalarParamRegion ∅) := ⟨hs, by simp, hz1⟩
  have hP : ∀ ℓ ∈ (∅ : Finset ℕ), Nat.Prime ℓ := fun ℓ hℓ => absurd hℓ (Finset.notMem_empty ℓ)
  have h := tendsto_scalarWeightSum_tprod_scalarLocalFactor ∅ hP hx (fun _ => (1 : ℂ))
  rw [tprod_primes_tsum_δ_mul_cpow_eq hs z]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  exact (tsum_tamagawaProportion_mul_cpow s z hX).symm

/-! ### Uniform bounds on the Dirichlet weight, and summability at a fixed height bound -/

/-- For real `σ ≥ 0` and every `m : ℕ`, `m^{-σ} ≤ 1`. -/
lemma natCast_rpow_neg_le_one {σ : ℝ} (hσ : 0 ≤ σ) (m : ℕ) : (m : ℝ) ^ (-σ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases eq_or_ne σ 0 with rfl | hσ0
    · simp
    · rw [Nat.cast_zero, Real.zero_rpow (neg_ne_zero.2 hσ0)]
      exact zero_le_one
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm) (neg_nonpos.2 hσ)

/-- For every `X ≥ 0`, the truncated proportions `m ↦ P_Tam(m; X)` are summable. -/
lemma summable_tamagawaProportion {X : ℝ} (hX : 0 ≤ X) :
    Summable fun m : ℕ => tamagawaProportion m X := by
  classical
  refine summable_of_ne_finset_zero
    (s := (finite_setOf_tamagawaProportion_ne_zero hX).toFinset) fun m hm => ?_
  by_contra h
  exact hm ((finite_setOf_tamagawaProportion_ne_zero hX).mem_toFinset.2 h)

/-- For `σ ≥ 0` and `X ≥ 0`, the real Dirichlet series `∑_m P_Tam(m; X) m^{-σ}` converges. -/
lemma summable_tamagawaProportion_mul_rpow {σ : ℝ} (hσ : 0 ≤ σ) {X : ℝ} (hX : 0 ≤ X) :
    Summable fun m : ℕ => tamagawaProportion m X * (m : ℝ) ^ (-σ) :=
  Summable.of_nonneg_of_le
    (fun m => mul_nonneg (tamagawaProportion_nonneg m X) (Real.rpow_nonneg (Nat.cast_nonneg m) _))
    (fun m => mul_le_of_le_one_right (tamagawaProportion_nonneg m X)
      (natCast_rpow_neg_le_one hσ m))
    (summable_tamagawaProportion hX)

/-- For `Re(s) ≥ 0` and `X ≥ 0`, the Dirichlet series `∑_m P_Tam(m; X) m^{-s}` is summable. -/
lemma summable_tamagawaProportion_mul_cpow {s : ℂ} (hs : 0 ≤ s.re) {X : ℝ} (hX : 0 ≤ X) :
    Summable fun m : ℕ => (tamagawaProportion m X : ℂ) * (m : ℂ) ^ (-s) :=
  (summable_tamagawaProportion hX).of_norm_bounded fun m => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (tamagawaProportion_nonneg m X)]
    exact mul_le_of_le_one_right (tamagawaProportion_nonneg m X)
      (norm_natCast_cpow_neg_le_one hs m)

/-! ### The Dirichlet series along the real axis -/

/-- At a real exponent `σ`, the Dirichlet series `∑_m P_Tam(m; X) m^{-σ}` computed in `ℂ` is the
coercion of the same sum computed in `ℝ`. -/
lemma tsum_tamagawaProportion_mul_cpow_ofReal (σ X : ℝ) :
    ∑' m : ℕ, (tamagawaProportion m X : ℂ) * (m : ℂ) ^ (-(σ : ℂ)) =
      ((∑' m : ℕ, tamagawaProportion m X * (m : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun m => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg m), Complex.ofReal_neg,
    Complex.ofReal_natCast]

/-- For real `σ ≥ 0`,

`lim_{X → ∞} ∑_m P_Tam(m; X) m^{-σ} = Re (∏'_p h_p(σ, 1, ()))`. -/
lemma tendsto_tsum_tamagawaProportion_mul_rpow (z : (∅ : Finset ℕ) → ℂ) {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun X : ℝ => ∑' m : ℕ, tamagawaProportion m X * (m : ℝ) ^ (-σ)) atTop
      (𝓝 (∏' p : ℕ, scalarLocalFactor ∅ p (σ : ℂ) 1 z).re) := by
  have hs : 0 ≤ ((σ : ℂ)).re := by simpa using hσ
  have h := tendsto_tsum_tamagawaProportion_mul_cpow hs
  rw [tprod_primes_tsum_δ_mul_cpow_eq hs z] at h
  have h2 : Tendsto
      (fun X : ℝ => (∑' m : ℕ, (tamagawaProportion m X : ℂ) * (m : ℂ) ^ (-(σ : ℂ))).re) atTop
      (𝓝 (∏' p : ℕ, scalarLocalFactor ∅ p (σ : ℂ) 1 z).re) :=
    (Complex.continuous_re.tendsto _).comp h
  refine h2.congr fun X => ?_
  rw [tsum_tamagawaProportion_mul_cpow_ofReal, Complex.ofReal_re]

/-- As the real exponent `σ` decreases to `0`, `Re (∏'_p h_p(σ, 1, ()))` tends to `1`. -/
lemma tendsto_re_tprod_scalarLocalFactor_ofReal (z : (∅ : Finset ℕ) → ℂ) :
    Tendsto (fun σ : ℝ => (∏' p : ℕ, scalarLocalFactor ∅ p (σ : ℂ) 1 z).re) (𝓝[>] (0 : ℝ))
      (𝓝 1) := by
  have hmaps : Set.MapsTo (fun σ : ℝ => ((σ : ℂ), (1 : ℂ), z)) (Set.Ici 0)
      (scalarParamRegion (∅ : Finset ℕ)) := fun σ hσ =>
    ⟨by simpa using hσ, by simp, fun ℓ => (Finset.notMem_empty _ ℓ.2).elim⟩
  have hg : Continuous fun σ : ℝ => (((σ : ℂ), (1 : ℂ), z) : ℂ × ℂ × ((∅ : Finset ℕ) → ℂ)) :=
    Complex.continuous_ofReal.prodMk continuous_const
  have hcont : ContinuousOn
      (fun σ : ℝ => ∏' p : ℕ, scalarLocalFactor ∅ p (σ : ℂ) 1 z) (Set.Ici 0) :=
    ContinuousOn.congr
      ((continuousOn_tprod_scalarLocalFactor (∅ : Finset ℕ)).comp hg.continuousOn hmaps)
      fun σ _ => rfl
  have h0 : Tendsto (fun σ : ℝ => ∏' p : ℕ, scalarLocalFactor ∅ p (σ : ℂ) 1 z)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := hcont 0 (Set.mem_Ici.2 le_rfl)
    rw [ContinuousWithinAt, Complex.ofReal_zero, tprod_scalarLocalFactor_empty_one_zero z] at h
    exact h.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
  simpa [Function.comp_def] using (Complex.continuous_re.tendsto (1 : ℂ)).comp h0

/-- For every `ε > 0` there is `σ > 0` with `1 - ε < Re (∏'_p h_p(σ, 1, ()))`. -/
lemma exists_pos_one_sub_lt_re_tprod (z : (∅ : Finset ℕ) → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℝ, 0 < σ ∧ 1 - ε < (∏' p : ℕ, scalarLocalFactor ∅ p (σ : ℂ) 1 z).re := by
  have h := (tendsto_re_tprod_scalarLocalFactor_ofReal z).eventually
    (eventually_gt_nhds (show (1 : ℝ) - ε < 1 by linarith))
  obtain ⟨σ, hσ1, hσ2⟩ := (h.and self_mem_nhdsWithin).exists
  exact ⟨σ, hσ2, hσ1⟩

/-! ### Tightness: no mass escapes to infinity -/

/-- For `σ > 0`, `M ≥ 1` and `X ≥ 4`,

`∑_m P_Tam(m; X) m^{-σ} ≤ 1 - (1 - M^{-σ}) ∑_{m ≥ M} P_Tam(m; X)`. -/
lemma tsum_tamagawaProportion_mul_rpow_le {σ : ℝ} (hσ : 0 < σ) {M : ℕ} (hM : 1 ≤ M) {X : ℝ}
    (hX : 4 ≤ X) :
    ∑' m : ℕ, tamagawaProportion m X * (m : ℝ) ^ (-σ) ≤
      1 - (1 - (M : ℝ) ^ (-σ)) * ∑' n : ℕ, tamagawaProportion (n + M) X := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hsum := summable_tamagawaProportion hX0
  have hsumw := summable_tamagawaProportion_mul_rpow hσ.le hX0
  have hsumT : Summable fun n : ℕ => tamagawaProportion (n + M) X :=
    (summable_nat_add_iff (f := fun m : ℕ => tamagawaProportion m X) M).2 hsum
  have hsplit := hsum.sum_add_tsum_nat_add M
  have hsplitw := hsumw.sum_add_tsum_nat_add M
  rw [tsum_tamagawaProportion_eq_one hX] at hsplit
  have hhead : ∑ m ∈ Finset.range M, tamagawaProportion m X * (m : ℝ) ^ (-σ)
      ≤ ∑ m ∈ Finset.range M, tamagawaProportion m X :=
    Finset.sum_le_sum fun m _ => mul_le_of_le_one_right (tamagawaProportion_nonneg m X)
      (natCast_rpow_neg_le_one hσ.le m)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have htail : ∑' n : ℕ, tamagawaProportion (n + M) X * ((n + M : ℕ) : ℝ) ^ (-σ)
      ≤ (M : ℝ) ^ (-σ) * ∑' n : ℕ, tamagawaProportion (n + M) X := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_)
      ((summable_nat_add_iff (f := fun m : ℕ => tamagawaProportion m X * (m : ℝ) ^ (-σ)) M).2
        hsumw) (hsumT.mul_left _)
    have hb : ((n + M : ℕ) : ℝ) ^ (-σ) ≤ (M : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hMpos (by push_cast; linarith) (neg_nonpos.2 hσ.le)
    rw [mul_comm ((M : ℝ) ^ (-σ))]
    exact mul_le_mul_of_nonneg_left hb (tamagawaProportion_nonneg _ _)
  rw [← hsplitw]
  linarith

/-- Tightness of the truncated proportions: for every `ε > 0` there is an `M` with

`∑_{m ≥ M} P_Tam(m; X) ≤ ε` for all large `X`,

the tail being written with the shifted index `n + M`. -/
theorem exists_tsum_tamagawaProportion_add_le {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ᶠ X : ℝ in atTop, ∑' n : ℕ, tamagawaProportion (n + M) X ≤ ε := by
  obtain ⟨σ, hσ0, hσF⟩ :=
    exists_pos_one_sub_lt_re_tprod (fun _ => (1 : ℂ)) (by positivity : (0 : ℝ) < ε / 4)
  obtain ⟨M, hM1, hMhalf⟩ : ∃ M : ℕ, 1 ≤ M ∧ (M : ℝ) ^ (-σ) ≤ 1 / 2 := by
    have hlt : ∀ᶠ x : ℝ in atTop, x ^ (-σ) < 1 / 2 :=
      (tendsto_rpow_neg_atTop hσ0).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    obtain ⟨x, hx1, hx2⟩ := (hlt.and (eventually_ge_atTop (1 : ℝ))).exists
    refine ⟨⌈x⌉₊, Nat.one_le_iff_ne_zero.2 fun h => ?_, ?_⟩
    · rw [Nat.ceil_eq_zero] at h
      linarith
    · refine le_trans (Real.rpow_le_rpow_of_nonpos (by linarith) (Nat.le_ceil x)
        (neg_nonpos.2 hσ0.le)) hx1.le
  refine ⟨M, ?_⟩
  have hlim := tendsto_tsum_tamagawaProportion_mul_rpow (fun _ => (1 : ℂ)) hσ0.le
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    hlim.eventually (eventually_gt_nhds (show
      (∏' p : ℕ, scalarLocalFactor ∅ p (σ : ℂ) 1 fun _ => (1 : ℂ)).re - ε / 4 <
        (∏' p : ℕ, scalarLocalFactor ∅ p (σ : ℂ) 1 fun _ => (1 : ℂ)).re by linarith))]
    with X hX hXD
  have hT0 : 0 ≤ ∑' n : ℕ, tamagawaProportion (n + M) X :=
    tsum_nonneg fun n => tamagawaProportion_nonneg _ _
  have hest := tsum_tamagawaProportion_mul_rpow_le hσ0 hM1 hX
  nlinarith [mul_nonneg hT0 (by linarith : (0 : ℝ) ≤ 1 / 2 - (M : ℝ) ^ (-σ))]

/-! ### The limiting densities form a probability distribution -/

/-- If each truncated proportion `X ↦ P_Tam(m; X)` converges, then every finite partial sum of the
limiting densities is at most `1`. -/
lemma sum_range_tamagawaDensity_le_one
    (hconv : ∀ m : ℕ, ∃ L : ℝ, Tendsto (tamagawaProportion m) atTop (𝓝 L)) (N : ℕ) :
    ∑ m ∈ Finset.range N, tamagawaDensity m ≤ 1 := by
  have h : Tendsto (fun X : ℝ => ∑ m ∈ Finset.range N, tamagawaProportion m X) atTop
      (𝓝 (∑ m ∈ Finset.range N, tamagawaDensity m)) :=
    tendsto_finsetSum _ fun m _ => tendsto_tamagawaProportion (hconv m)
  refine le_of_tendsto h ?_
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX
  calc ∑ m ∈ Finset.range N, tamagawaProportion m X
      ≤ ∑' m : ℕ, tamagawaProportion m X :=
        Summable.sum_le_tsum _ (fun m _ => tamagawaProportion_nonneg m X)
          (summable_tamagawaProportion (by linarith))
    _ = 1 := tsum_tamagawaProportion_eq_one hX

/-- If each truncated proportion `X ↦ P_Tam(m; X)` converges, the limiting densities are summable.
-/
theorem summable_tamagawaDensity_of_tendsto
    (hconv : ∀ m : ℕ, ∃ L : ℝ, Tendsto (tamagawaProportion m) atTop (𝓝 L)) :
    Summable tamagawaDensity :=
  summable_of_sum_range_le tamagawaDensity_nonneg
    (sum_range_tamagawaDensity_le_one hconv)

/-- If each truncated proportion `X ↦ P_Tam(m; X)` converges, the limiting densities have total
mass `∑_m P_Tam(m) = 1`. -/
theorem tsum_tamagawaDensity_eq_one_of_tendsto
    (hconv : ∀ m : ℕ, ∃ L : ℝ, Tendsto (tamagawaProportion m) atTop (𝓝 L)) :
    ∑' m : ℕ, tamagawaDensity m = 1 := by
  refine le_antisymm (Real.tsum_le_of_sum_range_le tamagawaDensity_nonneg
    (sum_range_tamagawaDensity_le_one hconv)) (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨M, hM⟩ := exists_tsum_tamagawaProportion_add_le hε
  have hlim : Tendsto (fun X : ℝ => ∑ m ∈ Finset.range M, tamagawaProportion m X) atTop
      (𝓝 (∑ m ∈ Finset.range M, tamagawaDensity m)) :=
    tendsto_finsetSum _ fun m _ => tendsto_tamagawaProportion (hconv m)
  have hge : 1 - ε ≤ ∑ m ∈ Finset.range M, tamagawaDensity m := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (4 : ℝ), hM] with X hX hT
    have hsplit := (summable_tamagawaProportion (by linarith : (0 : ℝ) ≤ X)).sum_add_tsum_nat_add M
    rw [tsum_tamagawaProportion_eq_one hX] at hsplit
    linarith
  have hle : ∑ m ∈ Finset.range M, tamagawaDensity m ≤ ∑' m : ℕ, tamagawaDensity m :=
    Summable.sum_le_tsum _ (fun m _ => tamagawaDensity_nonneg m)
      (summable_tamagawaDensity_of_tendsto hconv)
  linarith

/-! ### `L¹` convergence of the truncated proportions -/

/-- If each truncated proportion `X ↦ P_Tam(m; X)` converges, then
`∑_m (P_Tam(m) - P_Tam(m; X))⁺ → 0` as `X → ∞`. -/
lemma tendsto_tsum_posPart_of_tendsto
    (hconv : ∀ m : ℕ, ∃ L : ℝ, Tendsto (tamagawaProportion m) atTop (𝓝 L)) :
    Tendsto (fun X : ℝ => ∑' m : ℕ, max (tamagawaDensity m - tamagawaProportion m X) 0) atTop
      (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun (X : ℝ) (m : ℕ) => max (tamagawaDensity m - tamagawaProportion m X) 0)
    (g := fun _ : ℕ => (0 : ℝ)) (bound := tamagawaDensity)
    (summable_tamagawaDensity_of_tendsto hconv)
    (fun m => by
      have h2 : Tendsto (fun X : ℝ => max (tamagawaDensity m - tamagawaProportion m X) 0) atTop
          (𝓝 (max (tamagawaDensity m - tamagawaDensity m) 0)) :=
        ((continuous_id.max continuous_const).tendsto _).comp
          (tendsto_const_nhds.sub (tendsto_tamagawaProportion (hconv m)))
      simpa using h2)
    (Eventually.of_forall fun X m => by
      rw [Real.norm_of_nonneg (le_max_iff.2 (Or.inr le_rfl))]
      exact max_le (by linarith [tamagawaProportion_nonneg m X]) (tamagawaDensity_nonneg m))
  simpa using h

/-- If each truncated proportion `X ↦ P_Tam(m; X)` converges, then
`∑_m |P_Tam(m; X) - P_Tam(m)| → 0` as `X → ∞` (Scheffé's lemma). -/
lemma tendsto_tsum_abs_sub_of_tendsto
    (hconv : ∀ m : ℕ, ∃ L : ℝ, Tendsto (tamagawaProportion m) atTop (𝓝 L)) :
    Tendsto (fun X : ℝ => ∑' m : ℕ, |tamagawaProportion m X - tamagawaDensity m|) atTop (𝓝 0) := by
  have hP := summable_tamagawaDensity_of_tendsto hconv
  have key : ∀ᶠ X : ℝ in atTop, ∑' m : ℕ, |tamagawaProportion m X - tamagawaDensity m| =
      2 * ∑' m : ℕ, max (tamagawaDensity m - tamagawaProportion m X) 0 := by
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX
    have hπ := summable_tamagawaProportion (by linarith : (0 : ℝ) ≤ X)
    have hmax : Summable fun m : ℕ => max (tamagawaDensity m - tamagawaProportion m X) 0 :=
      Summable.of_nonneg_of_le (fun m => le_max_iff.2 (Or.inr le_rfl))
        (fun m => max_le (by linarith [tamagawaProportion_nonneg m X])
          (tamagawaDensity_nonneg m)) hP
    have hterm : ∀ m : ℕ, |tamagawaProportion m X - tamagawaDensity m| =
        2 * max (tamagawaDensity m - tamagawaProportion m X) 0 +
          (tamagawaProportion m X - tamagawaDensity m) := by
      intro m
      rcases le_total (tamagawaDensity m) (tamagawaProportion m X) with h | h
      · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
        ring
      · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
        ring
    rw [tsum_congr hterm, Summable.tsum_add (hmax.mul_left 2) (hπ.sub hP), tsum_mul_left,
      Summable.tsum_sub hπ hP, tsum_tamagawaProportion_eq_one hX,
      tsum_tamagawaDensity_eq_one_of_tendsto hconv]
    ring
  have h2 : Tendsto
      (fun X : ℝ => 2 * ∑' m : ℕ, max (tamagawaDensity m - tamagawaProportion m X) 0) atTop
      (𝓝 0) := by
    simpa using (tendsto_tsum_posPart_of_tendsto hconv).const_mul 2
  exact h2.congr' (key.mono fun X h => h.symm)

/-! ### The Dirichlet series, assuming convergence of the truncated proportions -/

/-- If each truncated proportion `X ↦ P_Tam(m; X)` converges, then for every `s` with `Re(s) ≥ 0`
the Dirichlet series `∑_m P_Tam(m) m^{-s}` converges absolutely. -/
theorem summable_norm_tamagawaDensity_mul_cpow_of_tendsto
    (hconv : ∀ m : ℕ, ∃ L : ℝ, Tendsto (tamagawaProportion m) atTop (𝓝 L)) {s : ℂ}
    (hs : 0 ≤ s.re) :
    Summable fun m : ℕ => ‖(tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)‖ := by
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    (summable_tamagawaDensity_of_tendsto hconv)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (tamagawaDensity_nonneg m)]
  exact mul_le_of_le_one_right (tamagawaDensity_nonneg m) (norm_natCast_cpow_neg_le_one hs m)

/-- If each truncated proportion `X ↦ P_Tam(m; X)` converges, then for every `s : ℂ` with
`Re(s) ≥ 0`,

`∑_{m ≥ 1} P_Tam(m) m^{-s} = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{-s})`. -/
theorem tsum_tamagawaDensity_mul_cpow_of_tendsto
    (hconv : ∀ m : ℕ, ∃ L : ℝ, Tendsto (tamagawaProportion m) atTop (𝓝 L)) {s : ℂ}
    (hs : 0 ≤ s.re) :
    ∑' m : ℕ, (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)
      = ∏' p : {q : ℕ // q.Prime},
          ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * (t : ℂ) ^ (-s) := by
  have hPc : Summable fun m : ℕ => (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s) :=
    Summable.of_norm (summable_norm_tamagawaDensity_mul_cpow_of_tendsto hconv hs)
  have hdiff : Tendsto (fun X : ℝ => (∑' m : ℕ, (tamagawaProportion m X : ℂ) * (m : ℂ) ^ (-s))
      - ∑' m : ℕ, (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun X => norm_nonneg _) ?_
      (tendsto_tsum_abs_sub_of_tendsto hconv)
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX
    have hX0 : (0 : ℝ) ≤ X := by linarith
    have hb : ∀ m : ℕ, ‖(tamagawaProportion m X : ℂ) * (m : ℂ) ^ (-s)
          - (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)‖
        ≤ |tamagawaProportion m X - tamagawaDensity m| := by
      intro m
      rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (norm_natCast_cpow_neg_le_one hs m)
    have habs : Summable fun m : ℕ => |tamagawaProportion m X - tamagawaDensity m| :=
      ((summable_tamagawaProportion hX0).sub (summable_tamagawaDensity_of_tendsto hconv)).abs
    have hnorms : Summable fun m : ℕ => ‖(tamagawaProportion m X : ℂ) * (m : ℂ) ^ (-s)
        - (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)‖ :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) hb habs
    rw [← Summable.tsum_sub (summable_tamagawaProportion_mul_cpow hs hX0) hPc]
    refine le_trans (norm_tsum_le_tsum_norm hnorms) ?_
    exact Summable.tsum_le_tsum hb hnorms habs
  have hconvD : Tendsto (fun X : ℝ => ∑' m : ℕ, (tamagawaProportion m X : ℂ) * (m : ℂ) ^ (-s))
      atTop (𝓝 (∑' m : ℕ, (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s))) := by
    simpa using hdiff.add_const (∑' m : ℕ, (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s))
  exact tendsto_nhds_unique hconvD (tendsto_tsum_tamagawaProportion_mul_cpow hs)

/-! ### The Dirichlet series and its Euler product -/

/-- For every `s : ℂ` with `Re(s) ≥ 0` the Dirichlet series `∑_{m ≥ 1} P_Tam(m) m^{-s}` of the
limiting densities converges absolutely. -/
@[bsd_tamagawa "T018n"]
theorem summable_norm_tamagawaDensity_mul_cpow {s : ℂ} (hs : 0 ≤ s.re) :
    Summable fun m : ℕ => ‖(tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)‖ :=
  summable_norm_tamagawaDensity_mul_cpow_of_tendsto exists_tendsto_tamagawaProportion hs

/-- For every `s : ℂ` with `Re(s) ≥ 0`,

`∑_{m ≥ 1} P_Tam(m) m^{-s} = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{-s})`,

with `P_Tam(m)` the limiting density `tamagawaDensity m` and `δ_p(t)` the local density of the
Tamagawa number at `p`. -/
@[bsd_tamagawa "T018n"]
theorem tsum_tamagawaDensity_mul_cpow {s : ℂ} (hs : 0 ≤ s.re) :
    ∑' m : ℕ, (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)
      = ∏' p : {q : ℕ // q.Prime},
          ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * (t : ℂ) ^ (-s) :=
  tsum_tamagawaDensity_mul_cpow_of_tendsto exists_tendsto_tamagawaProportion hs

end WeierstrassCurve
