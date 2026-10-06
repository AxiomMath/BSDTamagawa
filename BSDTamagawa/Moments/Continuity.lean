/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Moments.LocalFinite
public import BSDTamagawa.Moments.MultipliableConditional
public import BSDTamagawa.NumberTheory.TateTailLawUnconditional

/-!
# Continuity of the moment Euler product at `σ = 0`

For every `k : ℕ`, the product over the primes `∏_p G_p(k - σ)` of the moment local factors tends
to `∏_p G_p(k)` as `σ ↓ 0`, with no hypothesis on the tail law.

* **The pointwise limit at a fixed prime.** Tannery's theorem applies with the dominating family
  `t ↦ δ_p(t) t^k`, which is summable at every prime by
  `WeierstrassCurve.summable_δ_toReal_mul_rpow`.
* **A majorant of `‖G_p(k − σ) − 1‖` uniform in `σ ≥ 0`.** At `p ≥ 5` the uniform local bound
  `C_k/p²` applies. At `p = 2, 3`, `G_p(k − σ)` is the real sum `∑_t δ_p(t) t^{k−σ}`, which lies
  between `0` and the finite quantity `∑_t δ_p(t) t^k` for `σ ≥ 0`. The majorant equal to
  `C_k/p² + (1 + ∑_t δ_p(t) t^k)` at the primes below `5` and to `C_k/p²` above is summable, the
  correction having finite support.

## Main results

* `WeierstrassCurve.tendsto_tsum_δ_toReal_mul_rpow`: the pointwise limit of the real series.
* `WeierstrassCurve.tendsto_momentLocalFactor`: the pointwise limit of `G_p`.
* `WeierstrassCurve.tendsto_tprod_momentLocalFactor`: the limit of the products.

## Implementation notes

The limit is taken along `𝓝[>] 0`; a limit for `σ` restricted to `(0, 1]` follows by
`Filter.Tendsto.mono_left`.

Every sum is `∑'` and every product `∏'`, since `∑ᶠ` and `∏ᶠ` collapse to their neutral value on
infinite supports. The subtractions `G_p(x) − 1` and `k − σ` take place in `ℂ` and `ℝ`; `δ_p(t)` is
coerced out of `ℝ≥0∞` by `ENNReal.toReal` before any arithmetic.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

/-! ### Continuity of each local factor -/

/-- At a fixed prime `p`,

`lim_{σ ↓ 0} ∑_{t ≥ 1} δ_p(t) t^{k - σ} = ∑_{t ≥ 1} δ_p(t) t^{k}`. -/
theorem tendsto_tsum_δ_toReal_mul_rpow (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Tendsto (fun σ : ℝ => ∑' t : ℕ, (δ p t).toReal * (t : ℝ) ^ ((k : ℝ) - σ))
      (𝓝[>] 0) (𝓝 (∑' t : ℕ, (δ p t).toReal * (t : ℝ) ^ (k : ℝ))) := by
  refine tendsto_tsum_of_dominated_convergence
    (summable_δ_toReal_mul_rpow p (k : ℝ)) (fun t => ?_) ?_
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp only [δ_zero, ENNReal.toReal_zero, zero_mul]
      exact tendsto_const_nhds
    · have hne : ((t : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hc : Continuous fun σ : ℝ => (δ p t).toReal * (t : ℝ) ^ ((k : ℝ) - σ) :=
        continuous_const.mul (continuous_const.rpow
          (continuous_const.sub continuous_id) fun _ => Or.inl hne)
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  · filter_upwards [self_mem_nhdsWithin] with σ hσ t
    have hσ0 : (0 : ℝ) < σ := hσ
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp only [δ_zero, ENNReal.toReal_zero, zero_mul, norm_zero]
      exact le_refl 0
    · have hb : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg
        (Real.rpow_nonneg (by positivity) _))]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hb (by linarith)) ENNReal.toReal_nonneg

/-- At a fixed prime `p`, `lim_{σ ↓ 0} G_p(k - σ) = G_p(k)`. -/
theorem tendsto_momentLocalFactor (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Tendsto (fun σ : ℝ => momentLocalFactor p ((k : ℝ) - σ))
      (𝓝[>] 0) (𝓝 (momentLocalFactor p (k : ℝ))) := by
  simp only [momentLocalFactor_eq_ofReal]
  exact Tendsto.comp (Complex.continuous_ofReal.tendsto _)
    (tendsto_tsum_δ_toReal_mul_rpow p k)

/-! ### A summable majorant valid at every prime -/

/-- The correction to the majorant `C_k/p²` at the primes below `5`: it is `1 + ∑_t δ_p(t) t^k` at
`p < 5` and `0` from `p = 5` on. -/
noncomputable def momentSmallBound (k : ℕ) (q : {n : ℕ // n.Prime}) : ℝ :=
  if (q : ℕ) < 5 then 1 + ∑' t : ℕ, (@δ (q : ℕ) ⟨q.2⟩ t).toReal * (t : ℝ) ^ (k : ℝ) else 0

/-- The correction is nonnegative. -/
theorem momentSmallBound_nonneg (k : ℕ) (q : {n : ℕ // n.Prime}) : 0 ≤ momentSmallBound k q := by
  rw [momentSmallBound]
  split_ifs with h
  · have : Fact (q : ℕ).Prime := ⟨q.2⟩
    have := tsum_δ_toReal_mul_rpow_nonneg (q : ℕ) (k : ℝ)
    linarith
  · exact le_refl 0

/-- The correction `momentSmallBound k` is summable over the primes. -/
theorem summable_momentSmallBound (k : ℕ) : Summable (momentSmallBound k) := by
  have hfin : {q : {n : ℕ // n.Prime} | (q : ℕ) < 5}.Finite := by
    have hsub : {q : {n : ℕ // n.Prime} | (q : ℕ) < 5}
        ⊆ (Subtype.val : {n : ℕ // n.Prime} → ℕ) ⁻¹' Set.Iio 5 := fun q hq => hq
    exact Set.Finite.subset ((Set.finite_Iio 5).preimage Subtype.val_injective.injOn) hsub
  refine summable_of_hasFiniteSupport (hfin.subset fun q hq => ?_)
  by_contra hcon
  have h5 : ¬ ((q : ℕ) < 5) := hcon
  exact hq (by rw [momentSmallBound, ite_eq_right h5])

/-- The majorant `C_k/p² + momentSmallBound k p` of `‖G_p(k - σ) - 1‖`. -/
noncomputable def momentTailBound (k : ℕ) (q : {n : ℕ // n.Prime}) : ℝ :=
  momentBoundConst k / ((q : ℕ) : ℝ) ^ 2 + momentSmallBound k q

/-- The majorant `momentTailBound k` is summable over the primes. -/
theorem summable_momentTailBound (k : ℕ) : Summable (momentTailBound k) :=
  (summable_const_div_sq_prime (momentBoundConst k)).add (summable_momentSmallBound k)

/-- For every prime `q` and every `σ ≥ 0`, `‖G_q(k - σ) - 1‖ ≤ momentTailBound k q`. -/
theorem norm_momentLocalFactor_sub_one_le_momentTailBound (k : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (q : {n : ℕ // n.Prime}) :
    ‖momentLocalFactor (q : ℕ) ((k : ℝ) - σ) - 1‖ ≤ momentTailBound k q := by
  have hq : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hbig0 : 0 ≤ momentBoundConst k / ((q : ℕ) : ℝ) ^ 2 := by
    have := momentBoundConst_pos k
    positivity
  have hsmall0 := momentSmallBound_nonneg k q
  rcases Nat.lt_or_ge (q : ℕ) 5 with h | h
  · have hS0 : 0 ≤ ∑' t : ℕ, (δ (q : ℕ) t).toReal * (t : ℝ) ^ ((k : ℝ) - σ) :=
      tsum_δ_toReal_mul_rpow_nonneg (q : ℕ) ((k : ℝ) - σ)
    have hT0 : 0 ≤ ∑' t : ℕ, (δ (q : ℕ) t).toReal * (t : ℝ) ^ (k : ℝ) :=
      tsum_δ_toReal_mul_rpow_nonneg (q : ℕ) (k : ℝ)
    have hST : (∑' t : ℕ, (δ (q : ℕ) t).toReal * (t : ℝ) ^ ((k : ℝ) - σ))
        ≤ ∑' t : ℕ, (δ (q : ℕ) t).toReal * (t : ℝ) ^ (k : ℝ) := by
      refine Summable.tsum_le_tsum (fun t => ?_)
        (summable_δ_toReal_mul_rpow (q : ℕ) ((k : ℝ) - σ))
        (summable_δ_toReal_mul_rpow (q : ℕ) (k : ℝ))
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp [δ_zero]
      · have hb : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hb (by linarith)) ENNReal.toReal_nonneg
    rw [momentLocalFactor_eq_ofReal, momentTailBound, momentSmallBound, ite_eq_left h]
    have hnorm : ‖((∑' t : ℕ, (δ (q : ℕ) t).toReal * (t : ℝ) ^ ((k : ℝ) - σ) : ℝ) : ℂ) - 1‖
        = |(∑' t : ℕ, (δ (q : ℕ) t).toReal * (t : ℝ) ^ ((k : ℝ) - σ)) - 1| := by
      rw [show ((∑' t : ℕ, (δ (q : ℕ) t).toReal * (t : ℝ) ^ ((k : ℝ) - σ) : ℝ) : ℂ) - 1
          = (((∑' t : ℕ, (δ (q : ℕ) t).toReal * (t : ℝ) ^ ((k : ℝ) - σ)) - 1 : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, abs_le]
    exact ⟨by linarith, by linarith⟩
  · refine le_trans (norm_momentLocalFactor_sub_one_le_of_tailLaw (q : ℕ)
      (hasTailGeometricLaw_of_five_le h) k (by linarith)) ?_
    rw [momentTailBound]
    linarith

/-! ### Continuity of the product -/

/-- For every `k : ℕ`,

`lim_{σ ↓ 0} ∏_{p ∈ 𝒫} G_p(k - σ) = ∏_{p ∈ 𝒫} G_p(k)`,

the limit being taken along `𝓝[>] 0`. -/
@[bsd_tamagawa "T059h"]
theorem tendsto_tprod_momentLocalFactor (k : ℕ) :
    Tendsto (fun σ : ℝ => ∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) ((k : ℝ) - σ))
      (𝓝[>] 0) (𝓝 (∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ))) := by
  have key := tendsto_tprod_one_add_of_dominated_convergence
    (𝓕 := 𝓝[>] (0 : ℝ))
    (bound := momentTailBound k)
    (f := fun (σ : ℝ) (p : {q : ℕ // q.Prime}) => momentLocalFactor (p : ℕ) ((k : ℝ) - σ) - 1)
    (g := fun p : {q : ℕ // q.Prime} => momentLocalFactor (p : ℕ) (k : ℝ) - 1)
    (summable_momentTailBound k)
    (fun p => by
      have : Fact ((p : ℕ).Prime) := ⟨p.2⟩
      exact (tendsto_momentLocalFactor (p : ℕ) k).sub_const 1)
    (by
      filter_upwards [self_mem_nhdsWithin] with σ hσ p
      have hσ0 : (0 : ℝ) < σ := hσ
      exact norm_momentLocalFactor_sub_one_le_momentTailBound k hσ0.le p)
  have e : ∀ x : ℝ, (∏' p : {q : ℕ // q.Prime}, (1 + (momentLocalFactor (p : ℕ) x - 1)))
      = ∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) x :=
    fun x => tprod_congr fun _ => by ring
  rw [← e (k : ℝ)]
  exact Tendsto.congr (fun σ => e ((k : ℝ) - σ)) key

end WeierstrassCurve
