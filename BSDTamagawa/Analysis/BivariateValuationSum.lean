/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import BSDTamagawa.Attr

/-!
# A bivariate valuation sum

For distinct primes `r ≠ s` and a real `q ≥ 2`, the series `∑_{t ≥ 5} q^{-t} v_r(t) v_s(t)`
converges and satisfies `∑_{t ≥ 5} q^{-t} v_r(t) v_s(t) ≤ q^{-rs} / (1 - q^{-rs})²`, where
`v_p = padicValNat p` is the `p`-adic valuation. Only multiples of `rs` contribute, and the bound
is sharp in its leading term `t = rs`.

## Main definitions

* `BSDTamagawa.BivariateValuationSum.summand`: the summand `q^{-t} v_r(t) v_s(t)`, set to `0` for
  `t < 5`.
* `BSDTamagawa.BivariateValuationSum.major`: the majorant `(m+1) q^{-(m+1)rs}`.

## Main results

* `BSDTamagawa.BivariateValuationSum.valuation_prod_le`: `(1 + v_r(m))(1 + v_s(m)) ≤ m` for
  distinct primes `r, s` and `m ≥ 1`.
* `BSDTamagawa.BivariateValuationSum.summand_summable`: the series converges.
* `BSDTamagawa.BivariateValuationSum.main_theorem`: the upper bound above.

## Implementation notes

The series is indexed by `t : ℕ` with the summand set to `0` for `t < 5`. Since every contributing
`t` is a multiple of `rs ≥ 6`, the cutoff excludes no nonzero term.
-/

@[expose] public section

namespace BSDTamagawa.BivariateValuationSum

/-- The summand of the series: `q^{-t} · v_r(t) · v_s(t)` for `t ≥ 5`, and `0` otherwise. Here
`v_r = padicValNat r` and `v_s = padicValNat s`. -/
noncomputable def summand (r s : ℕ) (q : ℝ) (t : ℕ) : ℝ :=
  if 5 ≤ t then q ^ (-(t : ℤ)) * (padicValNat r t : ℝ) * (padicValNat s t : ℝ) else 0

/-- The majorant series, indexed by `m ≥ 0`, modeling the contributing term at `t = rs·(m+1)`: its
value is `(m+1) · q^{-(m+1)·rs}`. -/
noncomputable def major (rs : ℕ) (q : ℝ) (m : ℕ) : ℝ :=
  (m + 1 : ℝ) * q ^ (-((m + 1) * rs : ℤ))

/-- **Elementary power bound.** For `r ≥ 2` and any `a : ℕ`, `1 + a ≤ r^a`. -/
theorem one_add_le_pow (r a : ℕ) (hr : 2 ≤ r) : 1 + a ≤ r ^ a :=
  calc 1 + a ≤ 2 ^ a := by have := Nat.lt_two_pow_self (n := a); omega
    _ ≤ r ^ a := Nat.pow_le_pow_left hr a

/-- **Key termwise valuation bound.** For distinct primes `r ≠ s` and `m ≥ 1`,
`(1 + v_r(m)) · (1 + v_s(m)) ≤ m`. -/
theorem valuation_prod_le (r s m : ℕ) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hm : 1 ≤ m) :
    (1 + padicValNat r m) * (1 + padicValNat s m) ≤ m := by
  have hcop : Nat.Coprime (r ^ padicValNat r m) (s ^ padicValNat s m) :=
    ((Nat.coprime_primes hr hs).2 hrs).pow _ _
  calc (1 + padicValNat r m) * (1 + padicValNat s m)
      ≤ r ^ padicValNat r m * s ^ padicValNat s m :=
        Nat.mul_le_mul (one_add_le_pow r _ hr.two_le) (one_add_le_pow s _ hs.two_le)
    _ ≤ m := Nat.le_of_dvd hm
        (hcop.mul_dvd_of_dvd_of_dvd pow_padicValNat_dvd pow_padicValNat_dvd)

/-- Distinct primes have product at least `6`: both are `≥ 2` and they differ, so the larger is
`≥ 3`. -/
private lemma six_le_mul {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) :
    6 ≤ r * s := by
  have := hr.two_le
  have := hs.two_le
  rcases eq_or_ne r 2 with rfl | hne
  · omega
  · nlinarith [show 3 ≤ r by omega]

/-- **Support reduction.** For distinct primes `r, s`, `summand r s q t = 0` unless `r*s ∣ t`. -/
theorem summand_support (r s : ℕ) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (q : ℝ) (t : ℕ) (h : ¬ (r * s ∣ t)) : summand r s q t = 0 := by
  have hcop : Nat.Coprime r s := (Nat.coprime_primes hr hs).2 hrs
  have hnotboth : ¬ (r ∣ t ∧ s ∣ t) := fun ⟨hrt, hst⟩ =>
    h (hcop.mul_dvd_of_dvd_of_dvd hrt hst)
  rcases not_and_or.mp hnotboth with h' | h' <;>
    simp [summand, padicValNat.eq_zero_of_not_dvd h']

/-- **Termwise majorization at multiples of `rs`.** For distinct primes and `q ≥ 2`,
`summand r s q (r*s*(m+1)) ≤ major (r*s) q m`. -/
theorem summand_le_major_reindex (r s : ℕ) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (q : ℝ) (hq : 2 ≤ q) (m : ℕ) :
    summand r s q (r * s * (m + 1)) ≤ major (r * s) q m := by
  have hq0 : (0 : ℝ) < q := by linarith
  have h6 : 6 ≤ r * s := six_le_mul hr hs hrs
  have ht5 : 5 ≤ r * s * (m + 1) :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ m.succ_pos)
  have hm1 : (m + 1 : ℕ) ≠ 0 := by omega
  have hval : ∀ p p' : ℕ, p.Prime → p'.Prime → p ≠ p' →
      padicValNat p (p * p' * (m + 1)) = 1 + padicValNat p (m + 1) := by
    intro p p' hp hp' hpp'
    have : Fact (Nat.Prime p) := ⟨hp⟩
    rw [mul_assoc, padicValNat.mul hp.ne_zero (Nat.mul_ne_zero hp'.ne_zero hm1),
      padicValNat.mul hp'.ne_zero hm1, padicValNat.self hp.one_lt,
      padicValNat.eq_zero_of_not_dvd
        (hp.coprime_iff_not_dvd.1 ((Nat.coprime_primes hp hp').2 hpp'))]
    omega
  have hvs : padicValNat s (r * s * (m + 1)) = 1 + padicValNat s (m + 1) := by
    rw [mul_comm r s]
    exact hval s r hs hr (Ne.symm hrs)
  unfold summand major
  rw [ite_eq_left ht5, hval r s hr hs hrs, hvs,
    show (-(↑(r * s * (m + 1)) : ℤ)) = -((m + 1) * (r * s) : ℤ) by push_cast; ring]
  have hcast : ((1 + padicValNat r (m + 1) : ℕ) : ℝ) * ((1 + padicValNat s (m + 1) : ℕ) : ℝ)
      ≤ (m + 1 : ℝ) := by exact_mod_cast valuation_prod_le r s (m + 1) hr hs hrs (by omega)
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left hcast (zpow_pos hq0 _).le).trans_eq (mul_comm _ _)

/-- **Summability of the majorant.** For `q ≥ 2` and `rs ≥ 6`, the series `∑ (m+1) q^{-(m+1)rs}`
converges. -/
theorem major_summable (rs : ℕ) (q : ℝ) (hq : 2 ≤ q) (hrs : 6 ≤ rs) :
    Summable (major rs q) := by
  set x : ℝ := q ^ (-(rs : ℤ)) with hx
  have hq0 : (0 : ℝ) < q := by linarith
  have hxpos : 0 < x := by rw [hx]; positivity
  have hx1 : x < 1 := by
    rw [hx, zpow_neg, inv_lt_one_iff₀]
    exact Or.inr (one_lt_zpow₀ (by linarith) (by omega))
  have hnorm : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hxpos]
  have hterm : ∀ m : ℕ, major rs q m = ((m + 1 : ℕ) : ℝ) * x ^ (m + 1) := by
    intro m
    unfold major
    rw [hx, ← zpow_natCast (q ^ (-(rs : ℤ))) (m + 1), ← zpow_mul]
    congr 1 <;> push_cast <;> ring_nf
  exact ((summable_nat_add_iff 1).2
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable).congr fun m => (hterm m).symm

/-- **Closed form of the right-hand side.** For `q ≥ 2` and `rs ≥ 6`,
`∑_{k ≥ 0} (k+1) q^{-(k+1)·rs} = q^{-rs}/(1 - q^{-rs})^2`. -/
theorem rhs_closed_form (q : ℝ) (rs : ℕ) (hq : 2 ≤ q) (hrs : 6 ≤ rs) :
    (∑' k : ℕ, ((k + 1 : ℝ)) * q ^ (-((k + 1) * rs : ℤ)))
      = q ^ (-(rs : ℤ)) / (1 - q ^ (-(rs : ℤ))) ^ 2 := by
  set x : ℝ := q ^ (-(rs : ℤ)) with hx
  have hq0 : (0 : ℝ) < q := by linarith
  have hxpos : 0 < x := by rw [hx]; positivity
  have hx1 : x < 1 := by
    rw [hx, zpow_neg, inv_lt_one_iff₀]
    exact Or.inr (one_lt_zpow₀ (by linarith) (by omega))
  have hnorm : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hxpos]
  have hsummand : ∀ k : ℕ, ((k + 1 : ℝ)) * q ^ (-((k + 1) * rs : ℤ))
      = ((k + 1 : ℕ) : ℝ) * x ^ (k + 1) := by
    intro k
    rw [hx, ← zpow_natCast (q ^ (-(rs : ℤ))) (k + 1), ← zpow_mul]
    congr 1 <;> push_cast <;> ring_nf
  rw [tsum_congr hsummand, ← tsum_coe_mul_geometric_of_norm_lt_one hnorm,
    Summable.tsum_eq_zero_add (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable]
  simp

/-- The reindexing map `m ↦ rs·(m+1)` onto the positive multiples of `rs` is injective. -/
private lemma reindex_injective {r s : ℕ} (hr : r.Prime) (hs : s.Prime) :
    Function.Injective (fun m : ℕ => r * s * (m + 1)) := by
  intro m n hmn
  have := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hr.pos hs.pos) hmn
  omega

/-- **Off-range vanishing.** `summand` is supported on the range of the reindexing map
`m ↦ rs·(m+1)`. -/
private lemma summand_eq_zero_of_notMem_range {r s : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (q : ℝ) :
    ∀ t : ℕ, t ∉ Set.range (fun m : ℕ => r * s * (m + 1)) → summand r s q t = 0 := by
  intro t ht
  by_cases hdvd : r * s ∣ t
  · obtain ⟨k, rfl⟩ := hdvd
    obtain rfl | hk := Nat.eq_zero_or_pos k
    · simp [summand]
    · exact absurd ⟨k - 1, show r * s * (k - 1 + 1) = r * s * k by congr 1; omega⟩ ht
  · exact summand_support r s hr hs hrs q t hdvd

/-- **Summability of the reindexed summand.** For distinct primes `r, s` and `q ≥ 2`,
`m ↦ summand r s q (rs·(m+1))` is summable. -/
theorem summand_reindex_summable (r s : ℕ) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (q : ℝ) (hq : 2 ≤ q) :
    Summable (fun m : ℕ => summand r s q (r * s * (m + 1))) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have h6 : 6 ≤ r * s := six_le_mul hr hs hrs
  refine Summable.of_nonneg_of_le (fun m => ?_)
    (fun m => summand_le_major_reindex r s hr hs hrs q hq m) (major_summable (r * s) q hq h6)
  unfold summand
  split_ifs <;> positivity

/-- **Reindexing of the full tsum onto multiples of `rs`.** For distinct primes `r, s`,
`∑' t, summand r s q t = ∑' m, summand r s q (rs·(m+1))`. -/
theorem summand_tsum_reindex (r s : ℕ) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (q : ℝ) :
    (∑' t : ℕ, summand r s q t) = ∑' m : ℕ, summand r s q (r * s * (m + 1)) := by
  simpa using ((reindex_injective hr hs).tsum_eq (f := fun t : ℕ => summand r s q t)
    fun t ht => not_imp_comm.mp (summand_eq_zero_of_notMem_range hr hs hrs q t) ht).symm

/-- **Convergence.** For distinct primes `r ≠ s` and a real `q ≥ 2`, the series
`∑_{t ≥ 5} q^{-t} v_r(t) v_s(t)` is summable. -/
theorem summand_summable (r s : ℕ) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (q : ℝ) (hq : 2 ≤ q) :
    Summable (summand r s q) := by
  refine ((reindex_injective hr hs).summable_iff
    (summand_eq_zero_of_notMem_range hr hs hrs q)).1 ?_
  simpa [Function.comp_def] using summand_reindex_summable r s hr hs hrs q hq

/-- For distinct primes `r ≠ s` and a real `q ≥ 2`,
`∑_{t ≥ 5} q^{-t} v_r(t) v_s(t) ≤ q^{-rs} / (1 - q^{-rs})^2`. -/
@[bsd_tamagawa "T048"]
theorem main_theorem (r s : ℕ) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (q : ℝ) (hq : 2 ≤ q) :
    (∑' t : ℕ, summand r s q t)
      ≤ q ^ (-(r * s : ℤ)) / (1 - q ^ (-(r * s : ℤ))) ^ 2 := by
  have h6 : 6 ≤ r * s := six_le_mul hr hs hrs
  have hrhs : (∑' m : ℕ, major (r * s) q m)
      = q ^ (-(r * s : ℤ)) / (1 - q ^ (-(r * s : ℤ))) ^ 2 :=
    rhs_closed_form q (r * s) hq h6
  rw [summand_tsum_reindex r s hr hs hrs q, ← hrhs]
  exact Summable.tsum_mono (summand_reindex_summable r s hr hs hrs q hq)
    (major_summable (r * s) q hq h6)
    (fun m => summand_le_major_reindex r s hr hs hrs q hq m)

end BSDTamagawa.BivariateValuationSum
