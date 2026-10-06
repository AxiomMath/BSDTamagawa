/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.TamagawaLaw.MomentsFinite
public import BSDTamagawa.Moments.MarkovTailConditional

/-!
# The Markov tail bound for the limiting Tamagawa density

For every `k : ℕ` and every `M ≥ 1`,

`∑_{m ≥ M} P_Tam(m) ≤ M_k / M^{k}`,

where `M_k = ∑_{m ≥ 1} P_Tam(m) m^k` is the `k`th moment, which is finite. In particular the
cumulative tail `∑_{m ≥ M} P_Tam(m)` decays faster than every fixed negative power of `M`.

## Main results

* `WeierstrassCurve.summable_tamagawaDensity_succ_mul_pow`: the family `(P_Tam(m) m^{k})_{m ≥ 1}`
  is summable.
* `WeierstrassCurve.tsum_tamagawaDensity_tail_le`: the Markov tail bound.
* `WeierstrassCurve.exists_tsum_tamagawaDensity_tail_le`: a finite constant `C` with
  `∑_{m ≥ M} P_Tam(m) ≤ C / M^{k}` for every `M ≥ 1`.

## Implementation notes

The statement holds for every `k : ℕ`, including `k = 0`, where it reads
`∑_{m ≥ M} P_Tam(m) ≤ M_0`. Since `tamagawaMoment k` is a `tsum`, which is `0` on a divergent
family, the bound depends on the summability of the moment series.
-/

@[expose] public section

namespace WeierstrassCurve

/-- The family `(P_Tam(m) m^{k})_{m ≥ 1}` is summable, in the indexing `m = n + 1`; its terms being
nonnegative, it is absolutely summable. -/
theorem summable_tamagawaDensity_succ_mul_pow (k : ℕ) :
    Summable fun n : ℕ => tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k :=
  (summable_nat_add_iff 1).mpr (summable_tamagawaDensity_mul_pow k)

/-- For every `k : ℕ` and every `M ≥ 1`,

`∑_{m ≥ M} P_Tam(m) ≤ M_k / M^{k}`. -/
@[bsd_tamagawa "T059b"]
theorem tsum_tamagawaDensity_tail_le (k : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    (∑' n : ℕ, tamagawaDensity (n + M)) ≤ tamagawaMoment k / (M : ℝ) ^ k := by
  have hMk : (0 : ℝ) < (M : ℝ) ^ k := by positivity
  have hidx : ∀ n : ℕ, n + (M - 1) + 1 = n + M := fun n => by omega
  have hf : Summable fun n : ℕ => tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k :=
    summable_tamagawaDensity_succ_mul_pow k
  have hshift : Summable fun n : ℕ => tamagawaDensity (n + M) * ((n + M : ℕ) : ℝ) ^ k :=
    ((summable_nat_add_iff (M - 1)).mpr hf).congr fun n => by rw [hidx n]
  have htail : (∑' n : ℕ, tamagawaDensity (n + M) * ((n + M : ℕ) : ℝ) ^ k) ≤ tamagawaMoment k := by
    have hsplit := hf.sum_add_tsum_nat_add (M - 1)
    have hcongr : (∑' n : ℕ, tamagawaDensity (n + (M - 1) + 1)
          * ((n + (M - 1) + 1 : ℕ) : ℝ) ^ k)
        = ∑' n : ℕ, tamagawaDensity (n + M) * ((n + M : ℕ) : ℝ) ^ k :=
      tsum_congr fun n => by rw [hidx n]
    have hhead : (0 : ℝ) ≤ ∑ i ∈ Finset.range (M - 1),
        tamagawaDensity (i + 1) * ((i + 1 : ℕ) : ℝ) ^ k :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (tamagawaDensity_nonneg (i + 1)) (pow_nonneg (Nat.cast_nonneg _) k)
    rw [hcongr] at hsplit
    rw [tamagawaMoment, ← hsplit]
    linarith
  have hterm : ∀ n : ℕ, tamagawaDensity (n + M)
      ≤ tamagawaDensity (n + M) * ((n + M : ℕ) : ℝ) ^ k / (M : ℝ) ^ k := by
    intro n
    have h1 : (M : ℝ) ^ k ≤ ((n + M : ℕ) : ℝ) ^ k :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.le_add_left M n) k
    rw [le_div_iff₀ hMk]
    exact mul_le_mul_of_nonneg_left h1 (tamagawaDensity_nonneg (n + M))
  calc (∑' n : ℕ, tamagawaDensity (n + M))
      ≤ ∑' n : ℕ, tamagawaDensity (n + M) * ((n + M : ℕ) : ℝ) ^ k / (M : ℝ) ^ k :=
        Summable.tsum_le_tsum hterm (summable_tamagawaDensity_shift M)
          (hshift.div_const ((M : ℝ) ^ k))
    _ = (∑' n : ℕ, tamagawaDensity (n + M) * ((n + M : ℕ) : ℝ) ^ k) / (M : ℝ) ^ k := by
        simp only [div_eq_mul_inv]
        exact tsum_mul_right
    _ ≤ tamagawaMoment k / (M : ℝ) ^ k := by gcongr

/-- For every `k` there is a real constant `C` with `∑_{m ≥ M} P_Tam(m) ≤ C / M^{k}` for every
`M ≥ 1`. -/
@[bsd_tamagawa "T059b"]
theorem exists_tsum_tamagawaDensity_tail_le (k : ℕ) :
    ∃ C : ℝ, ∀ M : ℕ, 1 ≤ M → (∑' n : ℕ, tamagawaDensity (n + M)) ≤ C / (M : ℝ) ^ k :=
  ⟨tamagawaMoment k, fun _ hM => tsum_tamagawaDensity_tail_le k hM⟩

end WeierstrassCurve
