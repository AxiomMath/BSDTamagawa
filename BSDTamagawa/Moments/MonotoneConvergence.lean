/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.TamagawaLaw.LimitingDensity

/-!
# Monotone convergence of the truncated moments

For every integer `k ≥ 0`, in `[0, ∞]`,

`lim_{σ ↓ 0} ∑_{m ≥ 1} P_Tam(m) m^{k - σ} = ∑_{m ≥ 1} P_Tam(m) m^{k}`,

the right-hand side being the moment `M_k` when it is finite and `+∞` otherwise. Here `P_Tam` is
the limiting Tamagawa density. The proof is one application of `tendsto_order`: the upper bound is
termwise monotonicity in the exponent, and the lower bound is the monotone convergence theorem
`ENNReal.tsum_eq_iSup_sum` together with continuity of finite partial sums in `σ`.

## Main results

* `WeierstrassCurve.tendsto_tsum_ofReal_tamagawaDensity_mul_rpow`: the limit, along `𝓝[>] 0`.
* `WeierstrassCurve.toReal_tsum_ofReal_tamagawaDensity_mul_pow`: the right-hand side, when finite,
  is `M_k`.
* `WeierstrassCurve.summable_of_tsum_ofReal_ne_top`: a nonnegative real family whose `ℝ≥0∞`-valued
  sum is finite is summable.

## Implementation notes

The summands enter `ℝ≥0∞` through `ENNReal.ofReal`, which loses nothing since they are nonnegative.
The "`+∞` otherwise" clause needs no statement: an `ℝ≥0∞`-valued `tsum` of a non-summable
nonnegative family is `⊤`.
-/

@[expose] public section

open Filter Topology

namespace WeierstrassCurve

/-! ### The summand -/

/-- At `σ = 0` the summand is the moment's summand: `P_Tam(m) m^{k - 0} = P_Tam(m) m^{k}`, with the
left-hand exponent a real power and the right-hand one a natural power. -/
theorem ofReal_tamagawaDensity_mul_rpow_zero (k n : ℕ) :
    ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ ((k : ℝ) - 0))
      = ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k) := by
  rw [sub_zero, Real.rpow_natCast]

/-- The summand is nonincreasing in the truncation: for `σ ≥ 0` and `m ≥ 1`,

`P_Tam(m) m^{k - σ} ≤ P_Tam(m) m^{k}`. -/
theorem ofReal_tamagawaDensity_mul_rpow_le (k n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ ((k : ℝ) - σ))
      ≤ ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k) := by
  have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have h : (1 : ℕ) ≤ n + 1 := Nat.le_add_left 1 n
    exact_mod_cast h
  refine ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left ?_ (tamagawaDensity_nonneg (n + 1)))
  rw [← Real.rpow_natCast ((n + 1 : ℕ) : ℝ) k]
  exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)

/-- For `m ≥ 1`, the summand `σ ↦ P_Tam(m) m^{k - σ}` in `ℝ≥0∞` is continuous. -/
theorem continuous_ofReal_tamagawaDensity_mul_rpow (k n : ℕ) :
    Continuous fun σ : ℝ =>
      ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ ((k : ℝ) - σ)) :=
  ENNReal.continuous_ofReal.comp (continuous_const.mul
    ((continuous_const (y := ((n + 1 : ℕ) : ℝ))).rpow
      (continuous_const.sub continuous_id) fun _ => Or.inl (by positivity)))

/-- Each finite partial sum of the truncated moment tends, as `σ ↓ 0`, to the corresponding partial
sum of the moment. -/
theorem tendsto_sum_ofReal_tamagawaDensity_mul_rpow (k : ℕ) (s : Finset ℕ) :
    Tendsto (fun σ : ℝ => ∑ n ∈ s,
        ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ ((k : ℝ) - σ)))
      (𝓝[>] 0)
      (𝓝 (∑ n ∈ s,
        ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k))) := by
  have h := ((continuous_finsetSum s fun n _ =>
      continuous_ofReal_tamagawaDensity_mul_rpow k n).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  rwa [Finset.sum_congr rfl fun n _ => ofReal_tamagawaDensity_mul_rpow_zero k n] at h

/-! ### From a finite `ℝ≥0∞`-sum back to `ℝ` -/

/-- If `f ≥ 0` and `∑'_n ofReal (f n) ≠ ⊤`, then `f` is summable in `ℝ`. -/
theorem summable_of_tsum_ofReal_ne_top {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : (∑' n : ℕ, ENNReal.ofReal (f n)) ≠ ⊤) : Summable f := by
  have h' : Summable fun n : ℕ => (f n).toNNReal := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa [ENNReal.ofReal] using h
  exact (NNReal.summable_coe.2 h').congr fun n => Real.coe_toNNReal _ (hf n)

/-! ### Monotone convergence -/

/-- For every integer `k ≥ 0`, in `[0, ∞]`,

`lim_{σ ↓ 0} ∑_{m ≥ 1} P_Tam(m) m^{k - σ} = ∑_{m ≥ 1} P_Tam(m) m^{k}`,

both sums taken in `ℝ≥0∞` and the limit along `𝓝[>] 0`. -/
@[bsd_tamagawa "T059j"]
theorem tendsto_tsum_ofReal_tamagawaDensity_mul_rpow (k : ℕ) :
    Tendsto (fun σ : ℝ => ∑' n : ℕ,
        ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ ((k : ℝ) - σ)))
      (𝓝[>] 0)
      (𝓝 (∑' n : ℕ, ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k))) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · rw [ENNReal.tsum_eq_iSup_sum, lt_iSup_iff] at hl
    obtain ⟨s, hs⟩ := hl
    filter_upwards [(tendsto_sum_ofReal_tamagawaDensity_mul_rpow k s).eventually_const_lt hs]
      with σ hσ
    exact lt_of_lt_of_le hσ (ENNReal.sum_le_tsum s)
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact lt_of_le_of_lt
      (ENNReal.tsum_le_tsum fun n =>
        ofReal_tamagawaDensity_mul_rpow_le k n (le_of_lt hσ)) hu

/-- If `∑_{m ≥ 1} P_Tam(m) m^{k} ≠ ⊤` in `[0, ∞]`, then its real value is the moment `M_k`. -/
@[bsd_tamagawa "T059j"]
theorem toReal_tsum_ofReal_tamagawaDensity_mul_pow {k : ℕ}
    (h : (∑' n : ℕ, ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k)) ≠ ⊤) :
    (∑' n : ℕ, ENNReal.ofReal (tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k)).toReal
      = tamagawaMoment k := by
  have hnonneg : ∀ n : ℕ, 0 ≤ tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k := fun n =>
    mul_nonneg (tamagawaDensity_nonneg (n + 1)) (pow_nonneg (Nat.cast_nonneg _) k)
  have hsum : Summable fun n : ℕ => tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k :=
    summable_of_tsum_ofReal_ne_top hnonneg h
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum,
    ENNReal.toReal_ofReal (tsum_nonneg hnonneg), tamagawaMoment]

end WeierstrassCurve
