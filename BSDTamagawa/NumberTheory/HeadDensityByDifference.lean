/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.GOTTailRowWildPrimes

/-!
# The fourth head density from the other three

The densities `δ_p(t)` agree with the table `gotδ p t` for every `t ≥ 5` at every prime, so
`HasGOTDensities p` reduces to the four head values `t = 1, 2, 3, 4`.

Both `δ_p` and the table are probability distributions on `ℕ`, and the two agree at `t = 0` (both
vanish) and on the whole tail `t ≥ 5`. So the five terms `t = 0, 1, 2, 3, 4` have the same total on
each side, and any three of the four head values force the fourth.

## Main results

* `ENNReal.sum_range_eq_sum_range_of_tail_eq`: two `ℝ≥0∞`-valued families on `ℕ` with the same
  finite total and the same values beyond `N` have equal `Finset.range N` sums.
* `WeierstrassCurve.tsum_ofReal_gotδ`: the table, pushed into `ℝ≥0∞`, sums to `1`.
* `WeierstrassCurve.δ_head_sum_eq_gotδ_head_sum`: the density and the table have the same total
  on `t = 0, 1, 2, 3, 4`, at every prime.
* `WeierstrassCurve.δ_eq_ofReal_gotδ_of_other_three`: any three head values give the fourth.
* `WeierstrassCurve.δ_one_eq_ofReal_gotδ_of_two_three_four`,
  `WeierstrassCurve.δ_four_eq_ofReal_gotδ_of_one_two_three`: the specialisations to `t = 1` and
  `t = 4`.
* `WeierstrassCurve.hasGOTDensities_of_three_heads`: `HasGOTDensities p` follows from the head
  values at `t = 2, 3, 4`.

## Implementation notes

No subtraction in `ℝ≥0∞` is formed: it truncates at `0`, so an identity `δ_p(1) = 1 - (rest)` would
hold vacuously whenever the rest exceeded `1`. The five-term identity is additive, and the fourth
value is extracted with `ENNReal.add_left_inj` against a summand proved finite.

The split at `t = N` uses `Summable.sum_add_tsum_nat_add'`, the `AddCommMonoid` form; the unprimed
`Summable.sum_add_tsum_nat_add` requires an `AddCommGroup`, which `ℝ≥0∞` is not.
-/

open scoped ENNReal

@[expose] public section

namespace ENNReal

/-- **Two `ℝ≥0∞`-valued families on `ℕ` with a common finite total and a common tail have equal
heads.** If `f n = g n` for every `n ≥ N` and `∑' n, f n = ∑' n, g n = c` with `c ≠ ⊤`, then `f`
and `g` have the same sum over `Finset.range N`. -/
theorem sum_range_eq_sum_range_of_tail_eq {f g : ℕ → ℝ≥0∞} {N : ℕ} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (htail : ∀ n : ℕ, N ≤ n → f n = g n) (hf : ∑' n : ℕ, f n = c) (hg : ∑' n : ℕ, g n = c) :
    ∑ n ∈ Finset.range N, f n = ∑ n ∈ Finset.range N, g n := by
  have hsf : ∑ n ∈ Finset.range N, f n + ∑' n : ℕ, f (n + N) = ∑' n : ℕ, f n :=
    Summable.sum_add_tsum_nat_add' ENNReal.summable
  have hsg : ∑ n ∈ Finset.range N, g n + ∑' n : ℕ, g (n + N) = ∑' n : ℕ, g n :=
    Summable.sum_add_tsum_nat_add' ENNReal.summable
  have heq : ∑' n : ℕ, f (n + N) = ∑' n : ℕ, g (n + N) :=
    tsum_congr fun n => htail (n + N) (Nat.le_add_left N n)
  have hfin : ∑' n : ℕ, g (n + N) ≠ ⊤ :=
    ne_top_of_le_ne_top hc ((hg ▸ hsg) ▸ le_add_self)
  rw [heq] at hsf
  exact (ENNReal.add_left_inj hfin).1 ((hsf.trans hf).trans (hsg.trans hg).symm)

end ENNReal

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-- The table, pushed into `ℝ≥0∞`, is a probability distribution on `ℕ`. -/
theorem tsum_ofReal_gotδ : ∑' t : ℕ, ENNReal.ofReal (gotδ p t) = 1 := by
  have hprime : p.Prime := Fact.out
  have hsum : HasSum (gotδ p) 1 := hasSum_gotδ hprime
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => gotδ_nonneg hprime) hsum.summable, hsum.tsum_eq,
    ENNReal.ofReal_one]

/-- **The two distributions carry the same mass on `t = 0, 1, 2, 3, 4`**, unconditionally at every
prime. -/
theorem δ_head_sum_eq_gotδ_head_sum :
    ∑ t ∈ Finset.range 5, δ p t = ∑ t ∈ Finset.range 5, ENNReal.ofReal (gotδ p t) :=
  ENNReal.sum_range_eq_sum_range_of_tail_eq ENNReal.one_ne_top
    (fun _ ht => δ_eq_ofReal_gotδ_tail ht) (tsum_δ p) tsum_ofReal_gotδ

/-- **Any three of the four head values force the fourth**, at every prime.

If the density matches the table at every `1 ≤ t ≤ 4` other than `k`, it matches at `k`. -/
theorem δ_eq_ofReal_gotδ_of_other_three {k : ℕ} (hk : k ≤ 4)
    (h : ∀ t : ℕ, 1 ≤ t → t ≤ 4 → t ≠ k → δ p t = ENNReal.ofReal (gotδ p t)) :
    δ p k = ENNReal.ofReal (gotδ p k) := by
  have hmem : k ∈ Finset.range 5 := Finset.mem_range.2 (by omega)
  have key := δ_head_sum_eq_gotδ_head_sum (p := p)
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at key
  have hrest : ∑ t ∈ (Finset.range 5).erase k, δ p t
      = ∑ t ∈ (Finset.range 5).erase k, ENNReal.ofReal (gotδ p t) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨hne, hmem'⟩ := Finset.mem_erase.1 ht
    have : t < 5 := Finset.mem_range.1 hmem'
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · rw [δ_zero, gotδ_zero, ENNReal.ofReal_zero]
    · exact h t ht0 (by omega) hne
  rw [hrest] at key
  have hfin : ∑ t ∈ (Finset.range 5).erase k, ENNReal.ofReal (gotδ p t) ≠ ⊤ := by
    simp [ENNReal.sum_eq_top]
  exact (ENNReal.add_left_inj hfin).1 key

/-- **`t = 1` from `t = 2, 3, 4`.** -/
theorem δ_one_eq_ofReal_gotδ_of_two_three_four (h2 : δ p 2 = ENNReal.ofReal (gotδ p 2))
    (h3 : δ p 3 = ENNReal.ofReal (gotδ p 3)) (h4 : δ p 4 = ENNReal.ofReal (gotδ p 4)) :
    δ p 1 = ENNReal.ofReal (gotδ p 1) := by
  refine δ_eq_ofReal_gotδ_of_other_three (by omega) fun t ht1 ht htne => ?_
  interval_cases t
  · exact absurd rfl htne
  · exact h2
  · exact h3
  · exact h4

/-- **`t = 4` from `t = 1, 2, 3`.** -/
theorem δ_four_eq_ofReal_gotδ_of_one_two_three (h1 : δ p 1 = ENNReal.ofReal (gotδ p 1))
    (h2 : δ p 2 = ENNReal.ofReal (gotδ p 2)) (h3 : δ p 3 = ENNReal.ofReal (gotδ p 3)) :
    δ p 4 = ENNReal.ofReal (gotδ p 4) := by
  refine δ_eq_ofReal_gotδ_of_other_three (by omega) fun t ht1 ht htne => ?_
  interval_cases t
  · exact h1
  · exact h2
  · exact h3
  · exact absurd rfl htne

/-- **`HasGOTDensities p` from the head values at `t = 2, 3, 4`**, at every prime. -/
theorem hasGOTDensities_of_three_heads (h2 : δ p 2 = ENNReal.ofReal (gotδ p 2))
    (h3 : δ p 3 = ENNReal.ofReal (gotδ p 3)) (h4 : δ p 4 = ENNReal.ofReal (gotδ p 4)) :
    HasGOTDensities p := by
  refine hasGOTDensities_of_head fun t ht1 ht4 => ?_
  interval_cases t
  · exact δ_one_eq_ofReal_gotδ_of_two_three_four h2 h3 h4
  · exact h2
  · exact h3
  · exact h4

end WeierstrassCurve
