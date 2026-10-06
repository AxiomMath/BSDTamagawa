/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.AdditiveDecomposition

/-!
# Second moment of `Ω` and mixed valuations against `δ_p`

Assume the geometric tail law `δ_p(t) = a p^{-t}` for `t ≥ 5`, with `a ≤ 1`
(`WeierstrassCurve.HasTailGeometricLaw`). Then for every prime `p ≥ 8` and every pair of primes
`ℓ, ℓ'`,

  `∑_{t ≥ 1} δ_p(t) Ω(t)² ≤ 184/p²`   and   `∑_{t ≥ 1} δ_p(t) v_ℓ(t) v_{ℓ'}(t) ≤ 184/p²`.

The sum is split at `t = 5`. For `t ≤ 4` one has `Ω(t)² ≤ 4` and `δ_p(t) ≤ 9/p²` for `t ≠ 1`, which
bounds the head by `180/p²` at every prime. For the tail, `Ω(t) ≤ t` and
`∑_{s ≥ 0} (s+5)² p^{-(s+5)} ≤ 4p^{-2}` for `p ≥ 8`. The mixed sum is bounded termwise by the `Ω²`
sum, since `v_ℓ(t) ≤ Ω(t)` for a prime `ℓ`.

## Main results

* `WeierstrassCurve.sum_range_five_δ_mul_cardFactors_sq_le`: the head `∑_{t < 5} δ_p(t) Ω(t)²` is
  at most `180/p²` at every prime.
* `WeierstrassCurve.tsum_δ_mul_cardFactors_sq_le_of_tailLaw`: `∑_t δ_p(t) Ω(t)² ≤ 184/p²`.
* `WeierstrassCurve.tsum_δ_mul_padicValNat_mul_le_of_tailLaw`:
  `∑_t δ_p(t) v_ℓ(t) v_{ℓ'}(t) ≤ 184/p²`.
* `WeierstrassCurve.exists_second_moment_bounds_of_tailLaw`: both bounds with a single constant for
  all large primes, given the tail law at all large primes.

## Implementation notes

All sums are `tsum`s over `ℕ` in `ℝ≥0∞`, so no summability hypothesis is needed and a bound
`≤ C/p²` asserts finiteness. Since `δ_p(0) = 0` and `Ω(0) = Ω(1) = 0`, the sum over `ℕ` equals the
sum over `t ≥ 1`.
-/

@[expose] public section

open scoped ENNReal

namespace BSDTamagawa.SecondMoment

open BSDTamagawa.AdditiveMoment

/-! ### The arithmetic of the two weights -/

/-- `v_ℓ(t) ≤ Ω(t)` for a prime `ℓ`. Primality is needed: `padicValNat 4 16 = 2` while
`(16).factorization 4 = 0`. -/
theorem padicValNat_le_cardFactors {ℓ : ℕ} (hℓ : ℓ.Prime) (t : ℕ) :
    padicValNat ℓ t ≤ ArithmeticFunction.cardFactors t := by
  rw [← Nat.factorization_def t hℓ]
  exact BSDTamagawa.FirstMoment.factorization_le_cardFactors t ℓ

/-- `Ω(t) ≤ 2` for `t ≤ 4`. -/
theorem cardFactors_le_two_of_le_four {t : ℕ} (ht : t ≤ 4) :
    ArithmeticFunction.cardFactors t ≤ 2 := by
  interval_cases t <;>
    simp [cardFactors_two, cardFactors_three, cardFactors_four]

/-- `n² ≤ 4^n` in `ℝ≥0∞`. -/
theorem natCast_sq_le_four_pow (n : ℕ) : (n : ℝ≥0∞) ^ 2 ≤ (4 : ℝ≥0∞) ^ n := by
  calc (n : ℝ≥0∞) ^ 2 ≤ ((2 : ℝ≥0∞) ^ n) ^ 2 := by gcongr; exact natCast_le_two_pow n
    _ = (4 : ℝ≥0∞) ^ n := by rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num

/-- `4/p ≤ 1/2` in `ℝ≥0∞` for `p ≥ 8`. -/
theorem four_mul_inv_le_inv_two {p : ℕ} (hp : 8 ≤ p) :
    (4 : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.le_inv_iff_mul_le, mul_right_comm]
  calc (4 : ℝ≥0∞) * 2 * (p : ℝ≥0∞)⁻¹ = ((8 : ℕ) : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ := by norm_num
    _ ≤ 1 := natCast_mul_inv_le_one (by omega) hp

/-- For every `p ≥ 8`, `∑_{s ≥ 0} (s + 5)² p^{-(s+5)} ≤ 4 p^{-2}`. -/
theorem tsum_shift_natCast_sq_mul_inv_pow_le {p : ℕ} (hp : 8 ≤ p) :
    (∑' s : ℕ, ((s + 5 : ℕ) : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (s + 5))
      ≤ 4 * ((p : ℝ≥0∞)⁻¹) ^ 2 := by
  have hterm : ∀ s : ℕ, ((s + 5 : ℕ) : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (s + 5)
      ≤ (1024 * ((p : ℝ≥0∞)⁻¹) ^ 5) * ((2 : ℝ≥0∞)⁻¹) ^ s := by
    intro s
    calc ((s + 5 : ℕ) : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (s + 5)
        ≤ (4 : ℝ≥0∞) ^ (s + 5) * ((p : ℝ≥0∞)⁻¹) ^ (s + 5) :=
          mul_le_mul' (natCast_sq_le_four_pow (s + 5)) le_rfl
      _ = ((4 : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹) ^ 5 * ((4 : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹) ^ s := by
          rw [← mul_pow, ← pow_add, add_comm 5 s]
      _ ≤ (1024 * ((p : ℝ≥0∞)⁻¹) ^ 5) * ((2 : ℝ≥0∞)⁻¹) ^ s := by
          have h1 : ((4 : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹) ^ 5 = 1024 * ((p : ℝ≥0∞)⁻¹) ^ 5 := by
            rw [mul_pow]; norm_num
          have h2 : (4 : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ :=
            four_mul_inv_le_inv_two (p := p) hp
          rw [h1]
          gcongr
  have hgeom : ∑' s : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ s = 2 := by
    rw [ENNReal.tsum_geometric]; norm_num
  have hfinal : (2048 : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 5 ≤ 4 * ((p : ℝ≥0∞)⁻¹) ^ 2 := by
    have hinv : (p : ℝ≥0∞)⁻¹ ≤ (8 : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_le_inv.2 (by exact_mod_cast hp)
    have hsmall : (512 : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 3 ≤ 1 := by
      calc (512 : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 3 ≤ 512 * ((8 : ℝ≥0∞)⁻¹) ^ 3 := by gcongr
        _ = ((512 : ℕ) : ℝ≥0∞) * ((512 : ℕ) : ℝ≥0∞)⁻¹ := by
            rw [← ENNReal.inv_pow]; norm_num
        _ ≤ 1 := natCast_mul_inv_le_one (by norm_num) (by norm_num)
    calc (2048 : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ 5
        = 4 * ((512 * ((p : ℝ≥0∞)⁻¹) ^ 3) * ((p : ℝ≥0∞)⁻¹) ^ 2) := by ring
      _ ≤ 4 * (1 * ((p : ℝ≥0∞)⁻¹) ^ 2) := by gcongr
      _ = 4 * ((p : ℝ≥0∞)⁻¹) ^ 2 := by rw [one_mul]
  calc (∑' s : ℕ, ((s + 5 : ℕ) : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (s + 5))
      ≤ ∑' s : ℕ, (1024 * ((p : ℝ≥0∞)⁻¹) ^ 5) * ((2 : ℝ≥0∞)⁻¹) ^ s :=
        ENNReal.tsum_le_tsum hterm
    _ = (1024 * ((p : ℝ≥0∞)⁻¹) ^ 5) * ∑' s : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ s := ENNReal.tsum_mul_left
    _ = 2048 * ((p : ℝ≥0∞)⁻¹) ^ 5 := by rw [hgeom]; ring
    _ ≤ 4 * ((p : ℝ≥0∞)⁻¹) ^ 2 := hfinal

end BSDTamagawa.SecondMoment

namespace WeierstrassCurve

open BSDTamagawa.AdditiveMoment BSDTamagawa.SecondMoment

variable {p : ℕ} [Fact p.Prime]

/-! ### The head, unconditionally at every prime -/

/-- `∑_{t < 5} δ_p(t) Ω(t)² ≤ 180/p²` at every prime `p`. -/
theorem sum_range_five_δ_mul_cardFactors_sq_le :
    (∑ t ∈ Finset.range 5, δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞) ^ 2)
      ≤ 180 / (p : ℝ≥0∞) ^ 2 := by
  have hb : ∀ t ∈ Finset.range 5,
      δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞) ^ 2 ≤ 36 / (p : ℝ≥0∞) ^ 2 := by
    intro t ht
    rcases eq_or_ne t 1 with rfl | h1
    · simp
    · have h4 : t ≤ 4 := by
        have := Finset.mem_range.1 ht
        omega
      have hΩ : ((ArithmeticFunction.cardFactors t : ℕ) : ℝ≥0∞) ^ 2 ≤ 4 := by
        have hle : ((ArithmeticFunction.cardFactors t : ℕ) : ℝ≥0∞) ≤ 2 := by
          exact_mod_cast cardFactors_le_two_of_le_four h4
        calc ((ArithmeticFunction.cardFactors t : ℕ) : ℝ≥0∞) ^ 2 ≤ (2 : ℝ≥0∞) ^ 2 := by gcongr
          _ = 4 := by norm_num
      calc δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞) ^ 2
          ≤ (9 / (p : ℝ≥0∞) ^ 2) * 4 := mul_le_mul' (δ_le_nine_div_sq h1) hΩ
        _ = 36 / (p : ℝ≥0∞) ^ 2 := by
            simp only [div_eq_mul_inv]
            ring
  calc (∑ t ∈ Finset.range 5, δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞) ^ 2)
      ≤ ∑ _t ∈ Finset.range 5, (36 : ℝ≥0∞) / (p : ℝ≥0∞) ^ 2 := Finset.sum_le_sum hb
    _ = 180 / (p : ℝ≥0∞) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range]
        simp only [div_eq_mul_inv]
        ring

/-! ### The tail, granted the geometric law -/

/-- If `δ_p(t) = a p^{-t}` for `t ≥ 5` with `a ≤ 1`, then for every prime `p ≥ 8`
`∑_{s ≥ 0} δ_p(s+5) Ω(s+5)² ≤ 4 p^{-2}`. -/
theorem tsum_shift_δ_mul_cardFactors_sq_le_of_geometric (hp : 8 ≤ p) {a : ℝ≥0∞} (ha : a ≤ 1)
    (hgeom : ∀ t : ℕ, 5 ≤ t → δ p t = a * ((p : ℝ≥0∞)⁻¹) ^ t) :
    (∑' s : ℕ, δ p (s + 5) * (ArithmeticFunction.cardFactors (s + 5) : ℝ≥0∞) ^ 2)
      ≤ 4 * ((p : ℝ≥0∞)⁻¹) ^ 2 := by
  calc (∑' s : ℕ, δ p (s + 5) * (ArithmeticFunction.cardFactors (s + 5) : ℝ≥0∞) ^ 2)
      ≤ ∑' s : ℕ, a * (((s + 5 : ℕ) : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (s + 5)) := by
        refine ENNReal.tsum_le_tsum fun s => ?_
        rw [hgeom (s + 5) (by omega)]
        calc a * ((p : ℝ≥0∞)⁻¹) ^ (s + 5)
              * (ArithmeticFunction.cardFactors (s + 5) : ℝ≥0∞) ^ 2
            ≤ a * ((p : ℝ≥0∞)⁻¹) ^ (s + 5) * ((s + 5 : ℕ) : ℝ≥0∞) ^ 2 := by
              gcongr
              exact_mod_cast BSDTamagawa.FirstMoment.cardFactors_le_self (s + 5)
          _ = a * (((s + 5 : ℕ) : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (s + 5)) := by ring
    _ = a * ∑' s : ℕ, (((s + 5 : ℕ) : ℝ≥0∞) ^ 2 * ((p : ℝ≥0∞)⁻¹) ^ (s + 5)) :=
        ENNReal.tsum_mul_left
    _ ≤ 1 * (4 * ((p : ℝ≥0∞)⁻¹) ^ 2) := by
        gcongr
        exact tsum_shift_natCast_sq_mul_inv_pow_le hp
    _ = 4 * ((p : ℝ≥0∞)⁻¹) ^ 2 := one_mul _

/-! ### The second-moment bounds, granted the geometric tail law -/

/-- For every prime `p ≥ 8` satisfying the geometric tail law, `∑_t δ_p(t) Ω(t)² ≤ 184/p²`. -/
theorem tsum_δ_mul_cardFactors_sq_le_of_tailLaw (hp : 8 ≤ p) (h : HasTailGeometricLaw p) :
    (∑' t : ℕ, δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞) ^ 2)
      ≤ 184 / (p : ℝ≥0∞) ^ 2 := by
  obtain ⟨a, ha, hgeom⟩ := h
  rw [tsum_eq_sum_range_five_add_tsum_shift
    (fun t => δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞) ^ 2)]
  calc (∑ t ∈ Finset.range 5, δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞) ^ 2)
        + ∑' s : ℕ, δ p (s + 5) * (ArithmeticFunction.cardFactors (s + 5) : ℝ≥0∞) ^ 2
      ≤ 180 / (p : ℝ≥0∞) ^ 2 + 4 * ((p : ℝ≥0∞)⁻¹) ^ 2 := by
        gcongr
        · exact sum_range_five_δ_mul_cardFactors_sq_le
        · exact tsum_shift_δ_mul_cardFactors_sq_le_of_geometric hp ha hgeom
    _ ≤ 180 / (p : ℝ≥0∞) ^ 2 + 4 / (p : ℝ≥0∞) ^ 2 := by
        gcongr
        exact inv_pow_le_div_sq le_rfl 4
    _ = 184 / (p : ℝ≥0∞) ^ 2 := by
        simp only [div_eq_mul_inv]
        ring

/-- For every prime `p ≥ 8` satisfying the geometric tail law and all primes `ℓ, ℓ'`,
`∑_t δ_p(t) v_ℓ(t) v_{ℓ'}(t) ≤ 184/p²`. -/
theorem tsum_δ_mul_padicValNat_mul_le_of_tailLaw (hp : 8 ≤ p) (h : HasTailGeometricLaw p)
    {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) :
    (∑' t : ℕ, δ p t * (padicValNat ℓ t : ℝ≥0∞) * (padicValNat ℓ' t : ℝ≥0∞))
      ≤ 184 / (p : ℝ≥0∞) ^ 2 := by
  refine le_trans (ENNReal.tsum_le_tsum fun t => ?_)
    (tsum_δ_mul_cardFactors_sq_le_of_tailLaw hp h)
  have h1 : ((padicValNat ℓ t : ℕ) : ℝ≥0∞)
      ≤ (ArithmeticFunction.cardFactors t : ℝ≥0∞) := by
    exact_mod_cast padicValNat_le_cardFactors hℓ t
  have h2 : ((padicValNat ℓ' t : ℕ) : ℝ≥0∞)
      ≤ (ArithmeticFunction.cardFactors t : ℝ≥0∞) := by
    exact_mod_cast padicValNat_le_cardFactors hℓ' t
  calc δ p t * (padicValNat ℓ t : ℝ≥0∞) * (padicValNat ℓ' t : ℝ≥0∞)
      ≤ δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞)
          * (ArithmeticFunction.cardFactors t : ℝ≥0∞) := by gcongr
    _ = δ p t * (ArithmeticFunction.cardFactors t : ℝ≥0∞) ^ 2 := by ring

/-- If the geometric tail law holds at every prime `q ≥ p₀'`, there are `C > 0` and `p₀` such that
for every prime `q ≥ p₀` and all primes `ℓ, ℓ'`, both `∑_t δ_q(t) Ω(t)² ≤ C/q²` and
`∑_t δ_q(t) v_ℓ(t) v_{ℓ'}(t) ≤ C/q²`. -/
theorem exists_second_moment_bounds_of_tailLaw
    (h : ∃ p₀ : ℕ, ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q → HasTailGeometricLaw q) :
    ∃ C : ℝ≥0∞, ∃ p₀ : ℕ, 0 < C ∧ ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q →
      (∑' t : ℕ, δ q t * (ArithmeticFunction.cardFactors t : ℝ≥0∞) ^ 2) ≤ C / (q : ℝ≥0∞) ^ 2 ∧
        ∀ ℓ ℓ' : ℕ, ℓ.Prime → ℓ'.Prime →
          (∑' t : ℕ, δ q t * (padicValNat ℓ t : ℝ≥0∞) * (padicValNat ℓ' t : ℝ≥0∞))
            ≤ C / (q : ℝ≥0∞) ^ 2 := by
  obtain ⟨p₀, hlaw⟩ := h
  refine ⟨184, max p₀ 8, by norm_num, fun q _ hq => ?_⟩
  have hq8 : 8 ≤ q := le_of_max_le_right hq
  have hlq := hlaw q (le_of_max_le_left hq)
  exact ⟨tsum_δ_mul_cardFactors_sq_le_of_tailLaw (p := q) hq8 hlq,
    fun ℓ ℓ' hℓ hℓ' => tsum_δ_mul_padicValNat_mul_le_of_tailLaw (p := q) hq8 hlq hℓ hℓ'⟩

end WeierstrassCurve
