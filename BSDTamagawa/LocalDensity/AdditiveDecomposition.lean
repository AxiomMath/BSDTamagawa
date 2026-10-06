/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.FirstMoment

/-!
# A `p⁻²` bound on the `Ω`-weighted local density

This file bounds the `Ω`-weighted sum `∑_{t ≥ 1} δ_p(t) Ω(t)` of the scalar local densities by
splitting it at `t = 5`. The head is bounded at every prime `p`, using `δ_p(t) ≤ 9/p²` for
`t ∈ {2, 3, 4}`:

  `∑_{t < 5} δ_p(t) Ω(t) ≤ 36/p²`,

and the tail `∑_{s ≥ 0} δ_p(s+5) Ω(s+5)` is bounded under a geometric tail law
`δ_p(t) = a p^{-t}` (`t ≥ 5`, `a ≤ 1`), giving `∑_{t ≥ 1} δ_p(t) Ω(t) ≤ 37/p²` and the same bound
for `∑_t δ_p(t) v_ℓ(t)`, uniformly in `ℓ`, for `p ≥ 5`.

## Main definitions

* `WeierstrassCurve.HasTailGeometricLaw`: `δ_p(t) = a p^{-t}` for all `t ≥ 5`, for some `a ≤ 1`.

## Main results

* `WeierstrassCurve.sum_range_five_δ_mul_cardFactors_le`: `∑_{t < 5} δ_p(t) Ω(t) ≤ 36/p²` for every
  prime `p`.
* `WeierstrassCurve.tsum_δ_mul_cardFactors_le_of_tailLaw`: under the geometric tail law,
  `∑_{t ≥ 1} δ_p(t) Ω(t) ≤ 37/p²` for `p ≥ 5`.
* `WeierstrassCurve.exists_moment_bounds_of_tailLaw`: under the geometric tail law at all large
  primes, there are `C > 0` and `p₀` with `∑_t δ_p(t) Ω(t) ≤ C/p²` and `∑_t δ_p(t) v_ℓ(t) ≤ C/p²`
  for all primes `p ≥ p₀` and all `ℓ`.

## Implementation notes

All sums are `tsum`s of `ℝ≥0∞`-valued families, and no truncated subtraction occurs.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace BSDTamagawa.AdditiveMoment

/-! ### `Ω` at `t = 2, 3, 4` -/

/-- `Ω(2) = 1`. -/
theorem cardFactors_two : ArithmeticFunction.cardFactors 2 = 1 :=
  ArithmeticFunction.cardFactors_apply_prime Nat.prime_two

/-- `Ω(3) = 1`. -/
theorem cardFactors_three : ArithmeticFunction.cardFactors 3 = 1 :=
  ArithmeticFunction.cardFactors_apply_prime Nat.prime_three

/-- `Ω(4) = 2`. -/
theorem cardFactors_four : ArithmeticFunction.cardFactors 4 = 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
    ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two]

/-! ### Splitting a `ℝ≥0∞`-valued sum over `ℕ` at `t = 5` -/

/-- For `f : ℕ → ℝ≥0∞`, `∑_t f(t) = (∑_{t < 5} f(t)) + ∑_{s ≥ 0} f(s + 5)`. -/
theorem tsum_eq_sum_range_five_add_tsum_shift (f : ℕ → ℝ≥0∞) :
    ∑' t : ℕ, f t = (∑ t ∈ Finset.range 5, f t) + ∑' s : ℕ, f (s + 5) :=
  (ENNReal.summable.sum_add_tsum_nat_add' (k := 5)).symm

/-! ### The `ℝ≥0∞` arithmetic the tail estimate needs -/

/-- `m/n ≤ 1` in `ℝ≥0∞` for naturals `m ≤ n` with `n ≠ 0`. -/
theorem natCast_mul_inv_le_one {m n : ℕ} (hn : n ≠ 0) (h : m ≤ n) :
    (m : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ ≤ 1 := by
  have hmn : (m : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast h
  calc (m : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ ≤ (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ := by gcongr
    _ = 1 := ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hn) (ENNReal.natCast_ne_top n)

/-- `2/p ≤ 1/2` in `ℝ≥0∞` for `p ≥ 4`. -/
theorem two_mul_inv_le_inv_two {p : ℕ} (hp : 4 ≤ p) :
    (2 : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.le_inv_iff_mul_le, mul_right_comm]
  calc (2 : ℝ≥0∞) * 2 * (p : ℝ≥0∞)⁻¹ = ((4 : ℕ) : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ := by norm_num
    _ ≤ 1 := natCast_mul_inv_le_one (by omega) hp

/-- `n ≤ 2^n` in `ℝ≥0∞`. -/
theorem natCast_le_two_pow (n : ℕ) : (n : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ n := by
  calc (n : ℝ≥0∞) ≤ ((2 ^ n : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.lt_two_pow_self.le
    _ = (2 : ℝ≥0∞) ^ n := by push_cast; ring

/-- For every `p ≥ 5`, `∑_{s ≥ 0} (s + 5) p^{-(s+5)} ≤ p^{-2}`. -/
theorem tsum_shift_natCast_mul_inv_pow_le {p : ℕ} (hp : 5 ≤ p) :
    (∑' s : ℕ, ((s + 5 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ (s + 5)) ≤ ((p : ℝ≥0∞)⁻¹) ^ 2 := by
  have hterm : ∀ s : ℕ, ((s + 5 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ (s + 5)
      ≤ (32 * ((p : ℝ≥0∞)⁻¹) ^ 5) * ((2 : ℝ≥0∞)⁻¹) ^ s := by
    intro s
    calc ((s + 5 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ (s + 5)
        ≤ (2 : ℝ≥0∞) ^ (s + 5) * ((p : ℝ≥0∞)⁻¹) ^ (s + 5) := by
          gcongr
          exact natCast_le_two_pow _
      _ = ((2 : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹) ^ 5 * ((2 : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹) ^ s := by
          rw [← mul_pow, ← pow_add, add_comm 5 s]
      _ ≤ (32 * ((p : ℝ≥0∞)⁻¹) ^ 5) * ((2 : ℝ≥0∞)⁻¹) ^ s := by
          have h1 : ((2 : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹) ^ 5 = 32 * ((p : ℝ≥0∞)⁻¹) ^ 5 := by
            rw [mul_pow]; norm_num
          have h2 : (2 : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ :=
            two_mul_inv_le_inv_two (p := p) (by omega)
          rw [h1]
          gcongr
  have hgeom : ∑' s : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ s = 2 := by
    rw [ENNReal.tsum_geometric]; norm_num
  have hfinal : (64 : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 5 ≤ ((p : ℝ≥0∞)⁻¹) ^ 2 := by
    have hinv : (p : ℝ≥0∞)⁻¹ ≤ (5 : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_le_inv.2 (by exact_mod_cast hp)
    have hsmall : (64 : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 3 ≤ 1 := by
      calc (64 : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 3 ≤ 64 * ((5 : ℝ≥0∞)⁻¹) ^ 3 := by gcongr
        _ = ((64 : ℕ) : ℝ≥0∞) * ((125 : ℕ) : ℝ≥0∞)⁻¹ := by
            rw [← ENNReal.inv_pow]; norm_num
        _ ≤ 1 := natCast_mul_inv_le_one (by norm_num) (by norm_num)
    calc (64 : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 5
        = (64 * ((p : ℝ≥0∞)⁻¹) ^ 3) * ((p : ℝ≥0∞)⁻¹) ^ 2 := by ring
      _ ≤ 1 * ((p : ℝ≥0∞)⁻¹) ^ 2 := by gcongr
      _ = ((p : ℝ≥0∞)⁻¹) ^ 2 := one_mul _
  calc (∑' s : ℕ, ((s + 5 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ (s + 5))
      ≤ ∑' s : ℕ, (32 * ((p : ℝ≥0∞)⁻¹) ^ 5) * ((2 : ℝ≥0∞)⁻¹) ^ s := ENNReal.tsum_le_tsum hterm
    _ = (32 * ((p : ℝ≥0∞)⁻¹) ^ 5) * ∑' s : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ s := ENNReal.tsum_mul_left
    _ = 64 * ((p : ℝ≥0∞)⁻¹) ^ 5 := by rw [hgeom]; ring
    _ ≤ ((p : ℝ≥0∞)⁻¹) ^ 2 := hfinal

end BSDTamagawa.AdditiveMoment

namespace WeierstrassCurve

open BSDTamagawa.AdditiveMoment

variable {p : ℕ} [Fact p.Prime]

/-! ### Converting `C p^{-k}` to `C/p²` -/

/-- `C p^{-k} ≤ C/p²` in `ℝ≥0∞` for `k ≥ 2`. -/
theorem inv_pow_le_div_sq {k : ℕ} (hk : 2 ≤ k) (C : ℝ≥0∞) :
    C * ((p : ℝ≥0∞)⁻¹) ^ k ≤ C / (p : ℝ≥0∞) ^ 2 := by
  have hp1 : (p : ℝ≥0∞)⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.2 (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have hpow : ((p : ℝ≥0∞)⁻¹) ^ k ≤ ((p : ℝ≥0∞)⁻¹) ^ 2 := pow_le_pow_right_of_le_one' hp1 hk
  calc C * ((p : ℝ≥0∞)⁻¹) ^ k ≤ C * ((p : ℝ≥0∞)⁻¹) ^ 2 := by gcongr
    _ = C / (p : ℝ≥0∞) ^ 2 := by rw [div_eq_mul_inv, ENNReal.inv_pow]

/-! ### The `t`-indexed decomposition -/

/-- For every prime `p`, `∑_{t < 5} δ_p(t) Ω(t) ≤ 36/p²`. -/
theorem sum_range_five_δ_mul_cardFactors_le :
    (∑ t ∈ Finset.range 5, δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞))
      ≤ 36 / (p : ℝ≥0∞) ^ 2 := by
  calc ∑ t ∈ Finset.range 5, δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞)
      = δ p 2 + δ p 3 + 2 * δ p 4 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_succ, Finset.sum_range_one, cardFactors_two, cardFactors_three,
          cardFactors_four]
        simp only [ArithmeticFunction.map_zero, ArithmeticFunction.cardFactors_one, Nat.cast_zero,
          Nat.cast_one, Nat.cast_ofNat, mul_zero, mul_one, zero_add]
        rw [mul_comm (δ p 4)]
    _ ≤ 9 / (p : ℝ≥0∞) ^ 2 + 9 / (p : ℝ≥0∞) ^ 2 + 2 * (9 / (p : ℝ≥0∞) ^ 2) := by
        gcongr <;> exact δ_le_nine_div_sq (by norm_num)
    _ = 36 / (p : ℝ≥0∞) ^ 2 := by
        simp only [div_eq_mul_inv]
        ring

/-! ### The geometric tail law and its consequences -/

/-- The geometric tail law for `δ_p`: there is a constant `a ≤ 1` with `δ_p(t) = a p^{-t}` for
every `t ≥ 5`. -/
def HasTailGeometricLaw (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ a : ℝ≥0∞, a ≤ 1 ∧ ∀ t : ℕ, 5 ≤ t → δ p t = a * ((p : ℝ≥0∞)⁻¹) ^ t

/-- If `δ_p(t) = a p^{-t}` for `t ≥ 5`, then for every prime `p ≥ 5`

  `∑_{s ≥ 0} δ_p(s+5) Ω(s+5) ≤ a p^{-2}`. -/
theorem tsum_shift_δ_mul_cardFactors_le_of_geometric (hp : 5 ≤ p) {a : ℝ≥0∞}
    (hgeom : ∀ t : ℕ, 5 ≤ t → δ p t = a * ((p : ℝ≥0∞)⁻¹) ^ t) :
    (∑' s : ℕ, δ p (s + 5) * (ArithmeticFunction.cardFactors (s + 5) : ℝ≥0∞))
      ≤ a * ((p : ℝ≥0∞)⁻¹) ^ 2 := by
  calc (∑' s : ℕ, δ p (s + 5) * (ArithmeticFunction.cardFactors (s + 5) : ℝ≥0∞))
      ≤ ∑' s : ℕ, a * (((s + 5 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ (s + 5)) := by
        refine ENNReal.tsum_le_tsum fun s => ?_
        rw [hgeom (s + 5) (by omega)]
        calc a * ((p : ℝ≥0∞)⁻¹) ^ (s + 5) *
              (ArithmeticFunction.cardFactors (s + 5) : ℝ≥0∞)
            ≤ a * ((p : ℝ≥0∞)⁻¹) ^ (s + 5) * ((s + 5 : ℕ) : ℝ≥0∞) := by
              gcongr
              exact_mod_cast BSDTamagawa.FirstMoment.cardFactors_le_self (s + 5)
          _ = a * (((s + 5 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ (s + 5)) := by ring
    _ = a * ∑' s : ℕ, ((s + 5 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ (s + 5) := ENNReal.tsum_mul_left
    _ ≤ a * ((p : ℝ≥0∞)⁻¹) ^ 2 := by
        gcongr
        exact tsum_shift_natCast_mul_inv_pow_le hp

/-- For every prime `p ≥ 5` with `HasTailGeometricLaw p`, `∑_{t ≥ 1} δ_p(t) Ω(t) ≤ 37/p²`. -/
theorem tsum_δ_mul_cardFactors_le_of_tailLaw (hp : 5 ≤ p) (h : HasTailGeometricLaw p) :
    (∑' t : ℕ, δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞)) ≤ 37 / (p : ℝ≥0∞) ^ 2 := by
  obtain ⟨a, ha, hgeom⟩ := h
  rw [tsum_eq_sum_range_five_add_tsum_shift
    (fun t => δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞))]
  calc (∑ t ∈ Finset.range 5, δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞))
        + ∑' s : ℕ, δ p (s + 5) * (ArithmeticFunction.cardFactors (s + 5) : ℝ≥0∞)
      ≤ 36 / (p : ℝ≥0∞) ^ 2 + a * ((p : ℝ≥0∞)⁻¹) ^ 2 := by
        gcongr
        · exact sum_range_five_δ_mul_cardFactors_le
        · exact tsum_shift_δ_mul_cardFactors_le_of_geometric hp hgeom
    _ ≤ 36 / (p : ℝ≥0∞) ^ 2 + 1 / (p : ℝ≥0∞) ^ 2 := by
        gcongr
        calc a * ((p : ℝ≥0∞)⁻¹) ^ 2 ≤ 1 * ((p : ℝ≥0∞)⁻¹) ^ 2 := by gcongr
          _ = 1 / (p : ℝ≥0∞) ^ 2 := by rw [div_eq_mul_inv, ENNReal.inv_pow]
    _ = 37 / (p : ℝ≥0∞) ^ 2 := by
        simp only [div_eq_mul_inv]
        ring

/-- For every prime `p ≥ 5` with `HasTailGeometricLaw p` and every `ℓ`,
`∑_t δ_p(t) v_ℓ(t) ≤ 37/p²`. -/
theorem tsum_δ_mul_factorization_le_of_tailLaw (hp : 5 ≤ p) (h : HasTailGeometricLaw p) (ℓ : ℕ) :
    (∑' t : ℕ, δ p t * ((t.factorization) ℓ : ℝ≥0∞)) ≤ 37 / (p : ℝ≥0∞) ^ 2 :=
  (tsum_δ_mul_factorization_le_tsum_δ_mul_cardFactors ℓ).trans
    (tsum_δ_mul_cardFactors_le_of_tailLaw hp h)

/-- If the geometric tail law holds at every prime `q ≥ p₀'`, then there are `C > 0` and `p₀` such
that `∑_t δ_q(t) Ω(t) ≤ C/q²` and `∑_t δ_q(t) v_ℓ(t) ≤ C/q²` for every prime `q ≥ p₀` and every
`ℓ`. -/
theorem exists_moment_bounds_of_tailLaw
    (h : ∃ p₀ : ℕ, ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q → HasTailGeometricLaw q) :
    ∃ C : ℝ≥0∞, ∃ p₀ : ℕ, 0 < C ∧ ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q →
      (∑' t : ℕ, δ q t * (ArithmeticFunction.cardFactors t : ℝ≥0∞)) ≤ C / (q : ℝ≥0∞) ^ 2 ∧
        ∀ ℓ : ℕ, (∑' t : ℕ, δ q t * ((t.factorization) ℓ : ℝ≥0∞)) ≤ C / (q : ℝ≥0∞) ^ 2 := by
  obtain ⟨p₀, hlaw⟩ := h
  refine ⟨37, max p₀ 5, by norm_num, fun q _ hq => ?_⟩
  have hΩ := tsum_δ_mul_cardFactors_le_of_tailLaw (p := q) (le_of_max_le_right hq)
    (hlaw q (le_of_max_le_left hq))
  exact ⟨hΩ, fun ℓ => (tsum_δ_mul_factorization_le_tsum_δ_mul_cardFactors ℓ).trans hΩ⟩

end WeierstrassCurve
