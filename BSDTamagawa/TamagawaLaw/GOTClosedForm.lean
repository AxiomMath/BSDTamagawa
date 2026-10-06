/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.TailConstant

/-!
# The Griffin–Ono–Tsai closed forms for `δ_p(t)`

Lemma 3.1 of Griffin–Ono–Tsai gives explicit rational values of the local density `δ_p(t)` of the
Tamagawa number `t` at a prime `p`: four head values and a geometric tail `α_p p^{-t}` (`t ≥ 5`) at
`p = 2`, the same at `p = 3`, and a five-case rational closed form for `p ≥ 5`. This file records
that table as a real-valued function `gotδ`, proves that it is a probability distribution whose
tail constant satisfies `1/88572 ≤ α_p < 1/2`, and states the hypothesis `HasGOTDensities p` that
`δ_p` agrees with the table.

## Main definitions

* `WeierstrassCurve.gotα`: the tail constant `α_p` of the table.
* `WeierstrassCurve.gotδ`: the table, as a function of `p` and `t`.
* `WeierstrassCurve.HasGOTDensities`: the statement that `δ_p(t) = gotδ p t` for every `t`.

## Main results

* `WeierstrassCurve.hasSum_gotδ`: `∑_{t ≥ 1} gotδ p t = 1` at every prime `p`.
* `WeierstrassCurve.gotδ_nonneg`, `WeierstrassCurve.inv_88572_le_gotα`,
  `WeierstrassCurve.gotα_lt_half`: nonnegativity of the table and the bounds `1/88572 ≤ α_p < 1/2`.

## Implementation notes

Two entries of the printed table are corrected. At `p ≥ 5` and `t = 4` the paper prints the
numerator `3p² - 2p - 1`; the table uses `3p² - 2p + 1`, the printed value being incompatible with
total mass `1`. At `p = 3`, three of the four printed head values are off by
`(+3, −6, +3, 0)/29524`; this shift sums to zero, so it is invisible to the normalisation, and the
corrected values come from recomputing the Haar volumes of the fibres of Tate's algorithm at
`p = 3` (see `gotHeadThree`).

## References

* M. Griffin, K. Ono, W.-L. Tsai, *Tamagawa products of elliptic curves over `ℚ`*,
  Quart. J. Math. 72 (2021), Lemma 3.1.
-/

@[expose] public section

open scoped ENNReal

namespace WeierstrassCurve

/-! ### The table of Lemma 3.1 -/

/-- The cyclotomic-looking factor `p⁸ + p⁶ + p⁴ + p² + 1 = (p¹⁰ - 1)/(p² - 1)` common to the
denominators of the `p ≥ 5` column of the table. -/
noncomputable def gotQ (p : ℕ) : ℝ :=
  (p : ℝ) ^ 8 + (p : ℝ) ^ 6 + (p : ℝ) ^ 4 + (p : ℝ) ^ 2 + 1

/-- The factor `D_p := (p+1)² (p⁸ + p⁶ + p⁴ + p² + 1)`, the denominator of the `t = 1` and `t = 2`
entries of the `p ≥ 5` column. -/
noncomputable def gotD (p : ℕ) : ℝ := ((p : ℝ) + 1) ^ 2 * gotQ p

/-- The tail constant `α_p` of the table: for `t ≥ 5` the table is geometric,
`δ_p(t) = α_p p^{-t}`. It is `p⁸(p-1)²/(2(p¹⁰-1))` for `p ≥ 5`, `1/2046 = 1/(2 · 1023)` at `p = 2`
and `1/88572 = 1/(3 · 29524)` at `p = 3`. -/
noncomputable def gotα (p : ℕ) : ℝ :=
  if p = 2 then 1 / 2046
  else if p = 3 then 1 / 88572
  else (p : ℝ) ^ 8 * ((p : ℝ) - 1) ^ 2 / (2 * ((p : ℝ) ^ 10 - 1))

/-- The four head values `δ_2(1), …, δ_2(4)` of the table at `p = 2`. Only `t ∈ {1, 2, 3, 4}` is
meaningful. -/
noncomputable def gotHeadTwo (t : ℕ) : ℝ :=
  if t = 1 then 241 / 396 else if t = 2 then 7495 / 24552
  else if t = 3 then 1153 / 16368 else 171 / 10912

/-- The four head values `δ_3(1), …, δ_3(4)` of the table at `p = 3`. Only `t ∈ {1, 2, 3, 4}` is
meaningful.

Three of the four differ from the printed Lemma 3.1(2), which gives
`1924625/2125728, 510641/6377184, 7594/597861, 1193/652212`; the differences are
`(+3, −6, +3, 0)/29524`. The discrepancy is in the cell `a₄ ≡ 54 (mod 81)`,
`a₆ ≡ 27, 108, 135, 216 (mod 243)` of Case 9(iii) of the paper's analysis at `p = 3`, that is the
family `a₄ = -27t²`, `a₆ = 54t³ + 81s`, `3 ∤ st`, with `v₃(a₄) = v₃(a₆) = 3` and `v₃(Δ) = 10`, of
mass `4·3⁻⁹`: it has type `IV*` with Tamagawa number `3` (`a₆ ≡ 27, 135`) or `1` (`a₆ ≡ 108, 216`),
whereas the paper counts it as `III*` with Tamagawa number `2`. -/
noncomputable def gotHeadThree (t : ℕ) : ℝ :=
  if t = 1 then 1924841 / 2125728 else if t = 2 then 509345 / 6377184
  else if t = 3 then 30619 / 2391444 else 1193 / 652212

/-- The four head values `δ_p(1), …, δ_p(4)` of the table at `p ≥ 5`: the `t = 1` entry as `1`
minus a fraction over `6 D_p`, the `t = 2` entry over `2 D_p`, and the `t = 3`, `t = 4` entries
over `2(p+1) Q_p` and `6(p+1) Q_p`. Only `t ∈ {1, 2, 3, 4}` is meaningful. -/
noncomputable def gotHeadLarge (p t : ℕ) : ℝ :=
  if t = 1 then
    1 - (p : ℝ) * (6 * (p : ℝ) ^ 7 + 9 * (p : ℝ) ^ 6 + 9 * (p : ℝ) ^ 5 + 7 * (p : ℝ) ^ 4
      + 8 * (p : ℝ) ^ 3 + 7 * (p : ℝ) ^ 2 + 9 * (p : ℝ) + 6) / (6 * gotD p)
  else if t = 2 then
    (p : ℝ) * (2 * (p : ℝ) ^ 7 + 2 * (p : ℝ) ^ 6 + (p : ℝ) ^ 5 + (p : ℝ) ^ 4
      + 2 * (p : ℝ) ^ 3 + (p : ℝ) ^ 2 + 2 * (p : ℝ) + 2) / (2 * gotD p)
  else if t = 3 then (p : ℝ) ^ 2 * ((p : ℝ) ^ 4 + 1) / (2 * ((p : ℝ) + 1) * gotQ p)
  else (p : ℝ) ^ 3 * (3 * (p : ℝ) ^ 2 - 2 * (p : ℝ) + 1) / (6 * ((p : ℝ) + 1) * gotQ p)

/-- The table of Lemma 3.1 of Griffin–Ono–Tsai, as a real-valued function of the prime `p` and the
Tamagawa value `t`: `0` at `t = 0`, the geometric tail `α_p p^{-t}` for `t ≥ 5`, and the four head
values of the appropriate column for `t ∈ {1, 2, 3, 4}`. -/
noncomputable def gotδ (p t : ℕ) : ℝ :=
  if t = 0 then 0
  else if 5 ≤ t then gotα p / (p : ℝ) ^ t
  else if p = 2 then gotHeadTwo t
  else if p = 3 then gotHeadThree t
  else gotHeadLarge p t

variable {p t : ℕ}

/-! ### The entries of the table -/

/-- The table vanishes at `t = 0`. -/
theorem gotδ_zero : gotδ p 0 = 0 := by simp only [gotδ, ite_eq_left]

/-- The tail of the table is geometric with ratio `1/p`: `gotδ p t = α_p p^{-t}` for `t ≥ 5`. -/
theorem gotδ_tail (ht : 5 ≤ t) : gotδ p t = gotα p / (p : ℝ) ^ t := by
  simp only [gotδ]
  rw [ite_eq_right (show ¬ t = 0 by omega), ite_eq_left ht]

/-- The tail at `p = 2`: `δ_2(t) = 1/(2^{t+1} · 1023)` for `t ≥ 5`. -/
theorem gotδ_tail_two (ht : 5 ≤ t) : gotδ 2 t = 1 / ((2 : ℝ) ^ (t + 1) * 1023) := by
  rw [gotδ_tail ht, gotα, ite_eq_left rfl]
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hpow : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  rw [h2, pow_succ]
  field_simp
  ring

/-- The tail at `p = 3`: `δ_3(t) = 1/(3^{t+1} · 29524)` for `t ≥ 5`. -/
theorem gotδ_tail_three (ht : 5 ≤ t) : gotδ 3 t = 1 / ((3 : ℝ) ^ (t + 1) * 29524) := by
  rw [gotδ_tail ht, gotα, ite_eq_right (by norm_num : ¬ (3 : ℕ) = 2), ite_eq_left rfl]
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  have hpow : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
  rw [h3, pow_succ]
  field_simp
  ring

/-- The tail constant at `p ≥ 5`. -/
theorem gotα_of_five_le (hp : 5 ≤ p) :
    gotα p = (p : ℝ) ^ 8 * ((p : ℝ) - 1) ^ 2 / (2 * ((p : ℝ) ^ 10 - 1)) := by
  rw [gotα, ite_eq_right (show ¬ p = 2 by omega), ite_eq_right (show ¬ p = 3 by omega)]

/-- At `p ≥ 5` and `t ∈ {1, 2, 3, 4}` the table is the `p ≥ 5` head column. -/
theorem gotδ_of_five_le (hp : 5 ≤ p) (h0 : t ≠ 0) (h5 : ¬ 5 ≤ t) :
    gotδ p t = gotHeadLarge p t := by
  simp only [gotδ]
  rw [ite_eq_right h0, ite_eq_right h5, ite_eq_right (show ¬ p = 2 by omega),
    ite_eq_right (show ¬ p = 3 by omega)]

/-- The entry `δ_p(1)` at `p ≥ 5`. -/
theorem gotδ_one_of_five_le (hp : 5 ≤ p) :
    gotδ p 1 = 1 - (p : ℝ) * (6 * (p : ℝ) ^ 7 + 9 * (p : ℝ) ^ 6 + 9 * (p : ℝ) ^ 5
      + 7 * (p : ℝ) ^ 4 + 8 * (p : ℝ) ^ 3 + 7 * (p : ℝ) ^ 2 + 9 * (p : ℝ) + 6)
      / (6 * gotD p) := by
  rw [gotδ_of_five_le hp (by omega) (by omega), gotHeadLarge, ite_eq_left rfl]

/-- The entry `δ_p(2)` at `p ≥ 5`, accounting for the `I₂` rows and the additive types whose
component group has order `2`. -/
theorem gotδ_two_of_five_le (hp : 5 ≤ p) :
    gotδ p 2 = (p : ℝ) * (2 * (p : ℝ) ^ 7 + 2 * (p : ℝ) ^ 6 + (p : ℝ) ^ 5 + (p : ℝ) ^ 4
      + 2 * (p : ℝ) ^ 3 + (p : ℝ) ^ 2 + 2 * (p : ℝ) + 2) / (2 * gotD p) := by
  rw [gotδ_of_five_le hp (by omega) (by omega), gotHeadLarge,
    ite_eq_right (by omega : ¬ (2 : ℕ) = 1), ite_eq_left rfl]

/-- The entry `δ_p(3)` at `p ≥ 5`, accounting for the `I₃` rows and the additive types whose
component group has order `3`. -/
theorem gotδ_three_of_five_le (hp : 5 ≤ p) :
    gotδ p 3 = (p : ℝ) ^ 2 * ((p : ℝ) ^ 4 + 1) / (2 * ((p : ℝ) + 1) * gotQ p) := by
  rw [gotδ_of_five_le hp (by omega) (by omega), gotHeadLarge,
    ite_eq_right (by omega : ¬ (3 : ℕ) = 1), ite_eq_right (by omega : ¬ (3 : ℕ) = 2),
    ite_eq_left rfl]

/-- The entry `δ_p(4)` at `p ≥ 5`, accounting for the `I₄` rows, `I₀^*` and the `I_n^*` family,
with numerator `3p² - 2p + 1`. -/
theorem gotδ_four_of_five_le (hp : 5 ≤ p) :
    gotδ p 4 = (p : ℝ) ^ 3 * (3 * (p : ℝ) ^ 2 - 2 * (p : ℝ) + 1)
      / (6 * ((p : ℝ) + 1) * gotQ p) := by
  rw [gotδ_of_five_le hp (by omega) (by omega), gotHeadLarge,
    ite_eq_right (by omega : ¬ (4 : ℕ) = 1), ite_eq_right (by omega : ¬ (4 : ℕ) = 2),
    ite_eq_right (by omega : ¬ (4 : ℕ) = 3)]

/-! ### Positivity, and the uniform bounds on the tail constant -/

/-- `Q_p > 0`. -/
theorem gotQ_pos (hp : 2 ≤ p) : 0 < gotQ p := by
  have : (0 : ℝ) < (p : ℝ) := by positivity
  unfold gotQ
  positivity

/-- `D_p > 0`. -/
theorem gotD_pos (hp : 2 ≤ p) : 0 < gotD p := by
  have h := gotQ_pos hp
  have : (0 : ℝ) < (p : ℝ) := by positivity
  unfold gotD
  positivity

/-- A prime that is neither `2` nor `3` is at least `5`. -/
theorem five_le_of_prime (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  rcases Nat.lt_or_ge p 5 with h | h
  · interval_cases p <;> simp_all (config := { decide := true })
  · exact h

/-- The tail constant `α_p` is positive at every prime. -/
theorem gotα_pos (hp : p.Prime) : 0 < gotα p := by
  rw [gotα]
  split_ifs with h2 h3
  · norm_num
  · norm_num
  · have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast five_le_of_prime hp h2 h3
    have h10 : (1 : ℝ) < (p : ℝ) ^ 10 := one_lt_pow₀ (by linarith) (by norm_num)
    exact div_pos (mul_pos (pow_pos (by linarith) 8) (pow_pos (by linarith) 2)) (by linarith)

/-- The table is nonnegative at every prime. -/
theorem gotδ_nonneg (hp : p.Prime) : 0 ≤ gotδ p t := by
  have hp2 : 2 ≤ p := hp.two_le
  rw [gotδ]
  split_ifs with h0 h5 h2 h3
  · exact le_rfl
  · exact div_nonneg (gotα_pos hp).le (by positivity)
  · rw [gotHeadTwo]; split_ifs <;> norm_num
  · rw [gotHeadThree]; split_ifs <;> norm_num
  · have hp5 : 5 ≤ p := five_le_of_prime hp h2 h3
    have hr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
    have hQ := gotQ_pos hp2
    have hD := gotD_pos hp2
    rw [gotHeadLarge]
    split_ifs
    · rw [sub_nonneg, div_le_one (by linarith)]
      unfold gotD gotQ
      nlinarith [pow_pos (show (0:ℝ) < (p:ℝ) by linarith) 2,
        pow_pos (show (0:ℝ) < (p:ℝ) by linarith) 3,
        pow_pos (show (0:ℝ) < (p:ℝ) by linarith) 4,
        pow_pos (show (0:ℝ) < (p:ℝ) by linarith) 5,
        pow_pos (show (0:ℝ) < (p:ℝ) by linarith) 6,
        pow_pos (show (0:ℝ) < (p:ℝ) by linarith) 7,
        pow_pos (show (0:ℝ) < (p:ℝ) by linarith) 8,
        pow_pos (show (0:ℝ) < (p:ℝ) by linarith) 9,
        pow_pos (show (0:ℝ) < (p:ℝ) by linarith) 10]
    · positivity
    · positivity
    · refine div_nonneg (mul_nonneg (by positivity) ?_) (by positivity)
      nlinarith [sq_nonneg (3 * (p : ℝ) - 1)]

/-- The lower bound `α_p ≥ 1/88572`, uniformly over the primes, with equality at `p = 3`. -/
theorem inv_88572_le_gotα (hp : p.Prime) : (1 : ℝ) / 88572 ≤ gotα p := by
  rw [gotα]
  split_ifs with h2 h3
  · norm_num
  · norm_num
  · have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast five_le_of_prime hp h2 h3
    have h10 : (1 : ℝ) < (p : ℝ) ^ 10 := one_lt_pow₀ (by linarith) (by norm_num)
    have hB : (0 : ℝ) < 2 * ((p : ℝ) ^ 10 - 1) := by linarith
    have hquarter : (1 : ℝ) / 4 ≤ (p : ℝ) ^ 8 * ((p : ℝ) - 1) ^ 2 / (2 * ((p : ℝ) ^ 10 - 1)) := by
      rw [le_div_iff₀ hB]
      have hq : (0 : ℝ) ≤ (p : ℝ) ^ 2 - 4 * (p : ℝ) + 2 := by nlinarith
      nlinarith [mul_nonneg (pow_nonneg (show (0:ℝ) ≤ (p:ℝ) by linarith) 8) hq,
        pow_pos (show (0:ℝ) < (p:ℝ) by linarith) 8]
    linarith

/-- The upper bound `α_p < 1/2`, uniformly over the primes. -/
theorem gotα_lt_half (hp : p.Prime) : gotα p < 1 / 2 := by
  rw [gotα]
  split_ifs with h2 h3
  · norm_num
  · norm_num
  · have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast five_le_of_prime hp h2 h3
    have h10 : (1 : ℝ) < (p : ℝ) ^ 10 := one_lt_pow₀ (by linarith) (by norm_num)
    have hB : (0 : ℝ) < 2 * ((p : ℝ) ^ 10 - 1) := by linarith
    rw [div_lt_iff₀ hB]
    have h8 : (1 : ℝ) ≤ (p : ℝ) ^ 8 := one_le_pow₀ (by linarith)
    nlinarith [h8, pow_pos (show (0:ℝ) < (p:ℝ) by linarith) 8]

/-! ### The table has total mass one -/

/-- If the four head values and the tail sum `α_p/(p⁴(p-1))` add up to `1`, then the table has
total mass `1`. -/
theorem hasSum_gotδ_of_head_sum (hp : 2 ≤ p)
    (h : gotδ p 1 + gotδ p 2 + gotδ p 3 + gotδ p 4
      + gotα p / ((p : ℝ) ^ 4 * ((p : ℝ) - 1)) = 1) :
    HasSum (gotδ p) 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hne : (p : ℝ) ≠ 0 := hp0.ne'
  have hne1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hgeo : HasSum (fun n : ℕ ↦ ((p : ℝ)⁻¹) ^ n) (1 - (p : ℝ)⁻¹)⁻¹ :=
    hasSum_geometric_of_lt_one (by positivity) (by rw [inv_lt_one_iff₀]; right; exact hp1)
  have hfun : ∀ n : ℕ, gotδ p (n + 5) = gotα p / (p : ℝ) ^ 5 * ((p : ℝ)⁻¹) ^ n := by
    intro n
    rw [gotδ_tail (by omega), inv_pow, pow_add]
    field_simp
  have hv : gotα p / (p : ℝ) ^ 5 * (1 - (p : ℝ)⁻¹)⁻¹
      = gotα p / ((p : ℝ) ^ 4 * ((p : ℝ) - 1)) := by
    rw [eq_div_iff (by positivity)]
    field_simp
  have hshift : HasSum (fun n : ℕ ↦ gotδ p (n + 5))
      (gotα p / ((p : ℝ) ^ 4 * ((p : ℝ) - 1))) := by
    rw [← hv]
    simp only [hfun]
    exact hgeo.mul_left _
  have key := (hasSum_nat_add_iff (f := gotδ p) 5).mp hshift
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one, gotδ_zero] at key
  have hval : gotα p / ((p : ℝ) ^ 4 * ((p : ℝ) - 1))
      + (0 + gotδ p 1 + gotδ p 2 + gotδ p 3 + gotδ p 4) = 1 := by linarith
  rwa [hval] at key

/-- The head/tail identity at `p = 2`: `241/396 + 7495/24552 + 1153/16368 + 171/10912 + 1/32736
= 1`. -/
theorem gotδ_head_sum_two :
    gotδ 2 1 + gotδ 2 2 + gotδ 2 3 + gotδ 2 4
      + gotα 2 / (((2 : ℕ) : ℝ) ^ 4 * (((2 : ℕ) : ℝ) - 1)) = 1 := by
  norm_num [gotδ, gotHeadTwo, gotα]

/-- The head/tail identity at `p = 3`. -/
theorem gotδ_head_sum_three :
    gotδ 3 1 + gotδ 3 2 + gotδ 3 3 + gotδ 3 4
      + gotα 3 / (((3 : ℕ) : ℝ) ^ 4 * (((3 : ℕ) : ℝ) - 1)) = 1 := by
  norm_num [gotδ, gotHeadThree, gotα]

/-- The head/tail identity at `p ≥ 5`, as an identity of rational functions of `p`. -/
theorem gotδ_head_sum_of_five_le (hp : 5 ≤ p) :
    gotδ p 1 + gotδ p 2 + gotδ p 3 + gotδ p 4
      + gotα p / ((p : ℝ) ^ 4 * ((p : ℝ) - 1)) = 1 := by
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hne : (p : ℝ) ≠ 0 := by linarith
  have hne1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hne2 : (p : ℝ) + 1 ≠ 0 := by linarith
  have hQ : gotQ p ≠ 0 := (gotQ_pos (by omega)).ne'
  have hP10 : (p : ℝ) ^ 10 - 1 ≠ 0 := by
    have := one_lt_pow₀ (show (1 : ℝ) < (p : ℝ) by linarith) (show 10 ≠ 0 by norm_num)
    linarith
  rw [gotδ_one_of_five_le hp, gotδ_two_of_five_le hp, gotδ_three_of_five_le hp,
    gotδ_four_of_five_le hp, gotα_of_five_le hp]
  unfold gotD gotQ at *
  field_simp
  ring

/-- The table is a probability distribution: `∑_{t ≥ 1} gotδ p t = 1` at every prime `p`. -/
theorem hasSum_gotδ (hp : p.Prime) : HasSum (gotδ p) 1 := by
  by_cases h2 : p = 2
  · subst h2
    exact hasSum_gotδ_of_head_sum le_rfl gotδ_head_sum_two
  by_cases h3 : p = 3
  · subst h3
    exact hasSum_gotδ_of_head_sum (by norm_num) gotδ_head_sum_three
  exact hasSum_gotδ_of_head_sum hp.two_le (gotδ_head_sum_of_five_le (five_le_of_prime hp h2 h3))

/-! ### The hypothesis that `δ_p` agrees with the table -/

variable [Fact p.Prime]

/-- The statement that the local density `δ_p(t)` of the Tamagawa number at `p`, the `μ_p`-measure
of a fibre of Tate's algorithm, equals the table value `gotδ p t` for every `t`. -/
def HasGOTDensities (p : ℕ) [Fact p.Prime] : Prop := ∀ t : ℕ, δ p t = ENNReal.ofReal (gotδ p t)

end WeierstrassCurve
