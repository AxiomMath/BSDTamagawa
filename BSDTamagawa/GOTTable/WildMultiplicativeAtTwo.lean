/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildRowGoodAtTwo

/-!
# The multiplicative strata `(Iₙ, c)` at `p = 2`

This file places the multiplicative family at `p = 2` in the head rows: the split loci, on which
Tate's algorithm answers `(Iₙ, n)` for every `n ≥ 1`, and the non-split loci, on which it answers
`(Iₙ, 1)` for odd `n` and `(Iₙ, 2)` for even `n`. At each level the two halves have the same mass
`2^{-(n+11)}`, so the family totals `∑_{n ≥ 1} 2 · 2^{-(n+11)} = 2⁻¹⁰`.

A short model `y² = x³ + a₄x + a₆` over `ℤ_2` has `c₄ = -48a₄`, so `2 ∣ c₄` and Step 2 always takes
its additive branch: a short `ℤ_2`-model is never `2`-minimal with multiplicative reduction. Every
point of the family therefore descends exactly once: Steps 1–10 all pass, Step 11 divides the model
down to a general Weierstrass model `V`, and the reduction datum is read off `V`. There
`2⁴c₄(V) = -48a₄` makes `c₄(V) = -3a₄` a unit, so `V` is nodal; `2¹²Δ(V) = Δ` turns
`v₂(Δ) = n + 12` into `v₂(Δ(V)) = n`; and `2⁶c₆(V) = -1728b` with `a₆ = 2b` makes `-c₆(V) = 27b`,
so the split test of Step 2 is a condition on `b` modulo `8`.

Since `Δ = -2⁶(a₄³ + 27b²)`, the level condition `v₂(Δ) = n + 12` says `v₂(a₄³ + 27b²) = n + 6`. On
that shell `b` is odd and `a₄ ≡ 5 mod 8`; the multiplicative half is `b ≡ 3 mod 4`, while on
`b ≡ 1 mod 4` Step 7 answers `Iₘ*`. The split test `27b ≡ 1 mod 8` is `b ≡ 3 mod 8` and the
non-split test `27b ≡ 5 mod 8` is `b ≡ 7 mod 8`, and each forces the class of `a₄` modulo `16`:

    split      a₄ ≡  5 mod 16   a₆ ≡  6 mod 16   a₄ =  5 + 16α   b = 11 + 8α + 32k
    non-split  a₄ ≡ 13 mod 16   a₆ ≡ 14 mod 16   a₄ = 13 + 16α   b =  7 + 8α + 32k

The mass of a locus factors as the `a₄`-class `2⁻⁴`, the rescaling `a₆ = 2b` `2⁻¹`, and one of the
two shells of a square level set, `(1 - 2⁻¹) · 2^{-(n+5)}`: in total `2^{-(n+11)}`. Which shell
survives is decided by the square roots `s` of `γ = -a₄³/27`. On `a₄ ≡ 5 mod 16`, `γ ≡ 9 mod 16`
and `s ≡ ±3 mod 8`, so the shells are `b ≡ 3` and `b ≡ 5 mod 8`; on `a₄ ≡ 13 mod 16`,
`γ ≡ 1 mod 16` and `s ≡ ±1 mod 8`, so they are `b ≡ 7` and `b ≡ 1 mod 8`. In both cases the test
keeps exactly one of the two, and the one it discards is a `b ≡ 1 mod 4` shell; hence the split and
non-split halves have equal mass.

## Main definitions

* `WeierstrassCurve.multSplitLocusTwo`, `WeierstrassCurve.multNonSplitLocusTwo`: the split and
  non-split multiplicative loci at level `n`.
* `WeierstrassCurve.multNonSplitSetTwo`, `WeierstrassCurve.multNonSplitFstTwo`,
  `WeierstrassCurve.multNonSplitLevelSet`: the non-split test on `b`, the class `a₄ ≡ 13 mod 16`,
  and the non-split level set.

## Main results

* `WeierstrassCurve.multTwo_toZModPow_four_eq_six_iff` and
  `WeierstrassCurve.multTwo_toZModPow_four_eq_fourteen_iff`: the split and non-split tests as the
  `a₆`-classes `6` and `14` modulo `16`.
* `WeierstrassCurve.multTwo_exists_params_of_dvd_twelve` and
  `WeierstrassCurve.multTwo_exists_params_nonsplit_of_dvd_twelve`: the two parametrisations, under
  `2¹² ∣ Δ`.
* `WeierstrassCurve.TateAlgorithm.Step11.run_eq_ok_of_params_nonsplit_two`: Steps 1–10 all pass on
  `a₄ = 13 + 16α`, `a₆ = 2(7 + 8α + 32k)`, so Step 11 fires, at every level.
* `WeierstrassCurve.multTwo_run_eq_I_of_split` and `WeierstrassCurve.multTwo_run_eq_I_of_nonsplit`:
  the reduction data `(Iₙ, n)`, and `(Iₙ, 1)` or `(Iₙ, 2)` as `n` is odd or even.
* `WeierstrassCurve.multTwo_volume_splitLevelSet` and
  `WeierstrassCurve.multTwo_volume_nonSplitLevelSet`: the Haar mass of each level set, `2^{-(t+7)}`
  on its `a₄`-class and `0` on every other unit `a₄`, at every level `t`.
* `WeierstrassCurve.volume_multSplitLocusTwo_at_two`,
  `WeierstrassCurve.volume_multNonSplitLocusTwo_at_two`: both loci have mass `2^{-(n+11)}`.
* `WeierstrassCurve.multTwo_disjoint_nonsplit`: loci at distinct levels are disjoint.
-/

open scoped ENNReal
open MeasureTheory CommRing Ideal

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm BSDTamagawa.LocalConstancy

variable {p : ℕ} [Fact p.Prime]

/-! ### Two exhaustions over `ZMod 16` and `ZMod 4` -/

private theorem multTwo_zmod_a₄_of_cube (hp2 : p = 2) :
    ∀ A : ZMod (p ^ 4), A ^ 3 + 3 = 0 → A - 5 = 0 := by
  subst hp2; decide

private theorem multTwo_zmod_beta (hp2 : p = 2) :
    ∀ A B : ZMod (p ^ 2),
      23 + 75 * A + 240 * A ^ 2 + 256 * A ^ 3 + 81 * B + 108 * B ^ 2 = 0 → B - A - 1 = 0 := by
  subst hp2; decide

/-- `27` has an inverse in `ℤ_2`. -/
private theorem multTwo_exists_inv_twentySeven (hp2 : p = 2) : ∃ w : ℤ_[p], 27 * w = 1 := by
  obtain ⟨v, hv⟩ := (PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 27)
    (by rw [hp2]; norm_num)).exists_right_inv
  exact ⟨v, by rw [← hv]; norm_num⟩

/-! ### The split congruence as a residue condition on `a₆` -/

/-- **`a₆ ≡ 6 mod 16` is exactly `a₆ = 2b` with `b ∈ splitSetTwo 2`.** The split test
`27b ≡ 1 mod 8` is `b ≡ 3 mod 8`, and doubling turns that into a single class modulo `16`. -/
theorem multTwo_toZModPow_four_eq_six_iff (hp2 : p = 2) {a₆ : ℤ_[p]} :
    PadicInt.toZModPow 4 a₆ = (6 : ZMod (p ^ 4)) ↔
      ∃ b, a₆ = (p : ℤ_[p]) * b ∧ b ∈ splitSetTwo p := by
  have hπ : (p : ℤ_[p]) = 2 := by subst hp2; norm_num
  constructor
  · intro h
    obtain ⟨c, hc⟩ : (p : ℤ_[p]) ^ 4 ∣ a₆ - 6 := by
      rw [TateAlgorithm.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_ofNat, h, sub_self]
    rw [hπ] at hc
    exact ⟨3 + 8 * c, by rw [hπ]; linear_combination hc, ⟨10 + 27 * c, by rw [hπ]; ring⟩⟩
  · rintro ⟨b, rfl, hb⟩
    obtain ⟨u, hu⟩ : (p : ℤ_[p]) ^ 3 ∣ 27 * b - 1 := hb
    obtain ⟨w, hw⟩ := multTwo_exists_inv_twentySeven (p := p) hp2
    rw [hπ] at hu
    obtain ⟨c, hc⟩ : ∃ c : ℤ_[p], b - 3 = 8 * c :=
      ⟨w * (u - 10), by linear_combination w * hu + (3 - b) * hw⟩
    have hd : (p : ℤ_[p]) ^ 4 ∣ (p : ℤ_[p]) * b - 6 := ⟨c, by rw [hπ]; linear_combination 2 * hc⟩
    rwa [TateAlgorithm.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_ofNat, sub_eq_zero] at hd

/-! ### The parametrisation, at level `2 ^ 12` -/

/-- **The split locus at level `2 ^ 12`, parametrised**: `a₄ = 5 + 16α`, `b = 11 + 8α + 32k`. The
value of `a₄` modulo `16` comes from `2 ^ 4 ∣ a₄ ^ 3 + 3`, and the relation `β ≡ α + 1 mod 4` from
`2 ^ 2 ∣ E`. -/
theorem multTwo_exists_params_of_dvd_twelve (hp2 : p = 2) {a₄ a₆ b : ℤ_[p]}
    (ha₆ : a₆ = 2 * b) (hsplit : b ∈ splitSetTwo p)
    (hΔ : (p : ℤ_[p]) ^ 12 ∣ (ofShortNF a₄ a₆).Δ) :
    ∃ α k : ℤ_[p], a₄ = 5 + 16 * α ∧ b = 11 + 8 * α + 32 * k := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hπ : (p : ℤ_[p]) = 2 := by subst hp2; norm_num
  obtain ⟨w, hw⟩ := multTwo_exists_inv_twentySeven (p := p) hp2
  obtain ⟨u, hu⟩ : (p : ℤ_[p]) ^ 3 ∣ 27 * b - 1 := hsplit
  rw [hπ] at hu
  obtain ⟨β, hβ⟩ : ∃ β : ℤ_[p], b = 3 + 8 * β :=
    ⟨w * (u - 10), by linear_combination w * hu + (3 - b) * hw⟩
  obtain ⟨γ, hγ⟩ : (p : ℤ_[p]) ^ 6 ∣ a₄ ^ 3 + 27 * b ^ 2 := by
    have hkey : (ofShortNF a₄ a₆).Δ = (p : ℤ_[p]) ^ 6 * (-(a₄ ^ 3 + 27 * b ^ 2)) := by
      rw [ofShortNF_Δ, ha₆, hπ]; ring
    rw [hkey, show (12 : ℕ) = 6 + 6 from rfl, pow_add,
      mul_dvd_mul_iff_left (pow_ne_zero 6 hϖ)] at hΔ
    exact dvd_neg.1 hΔ
  rw [hπ] at hγ
  obtain ⟨α, hα⟩ : (p : ℤ_[p]) ^ 4 ∣ a₄ - 5 := by
    have h16 : (p : ℤ_[p]) ^ 4 ∣ a₄ ^ 3 + 3 := by
      refine ⟨4 * γ - (15 + 81 * β + 108 * β ^ 2), ?_⟩
      rw [hπ, hβ] at *
      linear_combination hγ
    rw [TateAlgorithm.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_ofNat]
    refine multTwo_zmod_a₄_of_cube hp2 _ ?_
    have hz := (TateAlgorithm.pow_dvd_iff_toZModPow_eq_zero 4 _).1 h16
    rwa [map_add, map_pow, map_ofNat] at hz
  rw [hπ] at hα
  have ha₄ : a₄ = 5 + 16 * α := by linear_combination hα
  have h16ne : (16 : ℤ_[p]) ≠ 0 := by
    rw [show (16 : ℤ_[p]) = (p : ℤ_[p]) ^ 4 from by rw [hπ]; norm_num]
    exact pow_ne_zero 4 hϖ
  have hE : (23 : ℤ_[p]) + 75 * α + 240 * α ^ 2 + 256 * α ^ 3 + 81 * β + 108 * β ^ 2 = 4 * γ := by
    refine mul_left_cancel₀ h16ne ?_
    rw [ha₄, hβ] at hγ
    linear_combination hγ
  obtain ⟨k, hk⟩ : (p : ℤ_[p]) ^ 2 ∣ β - α - 1 := by
    rw [TateAlgorithm.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_sub, map_one]
    refine multTwo_zmod_beta hp2 _ _ ?_
    have hd : (p : ℤ_[p]) ^ 2 ∣ 23 + 75 * α + 240 * α ^ 2 + 256 * α ^ 3 + 81 * β + 108 * β ^ 2 :=
      ⟨γ, by rw [hπ]; linear_combination hE⟩
    have hz := (TateAlgorithm.pow_dvd_iff_toZModPow_eq_zero 2 _).1 hd
    rwa [map_add, map_add, map_add, map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_mul,
      map_pow, map_pow, map_pow, map_ofNat, map_ofNat, map_ofNat, map_ofNat, map_ofNat,
      map_ofNat] at hz
  rw [hπ] at hk
  exact ⟨α, k, ha₄, by rw [hβ]; linear_combination 8 * hk⟩

/-! ### The second run: the descended curve is nodal and its tangent quadratic splits -/

/-- `-3` is a unit of `ℤ_2`. -/
private theorem multTwo_isUnit_neg_three (hp2 : p = 2) : IsUnit (-3 : ℤ_[p]) := by
  have h := PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 3) (by rw [hp2]; norm_num)
  simpa using h.neg

/-- Every member of `splitSetTwo 2` is a unit: `27b ≡ 1 mod 8` forces `b` odd. -/
private theorem multTwo_isUnit_of_mem_splitSetTwo {b : ℤ_[p]} (hb : b ∈ splitSetTwo p) :
    IsUnit b := by
  refine not_not.1 fun hnu => ?_
  obtain ⟨k, hk⟩ := PadicInt.dvd_iff_not_isUnit.2 hnu
  have hd1 : (p : ℤ_[p]) ∣ 27 * b - 1 := (dvd_pow_self _ three_ne_zero).trans hb
  have hd2 : (p : ℤ_[p]) ∣ 27 * b := ⟨27 * k, by rw [hk]; ring⟩
  exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_sub hd2 hd1))

/-- **The split multiplicative datum `(Iₙ, n)` at `p = 2`, for every `n ≥ 1`.** On the descended
curve `V`, `2⁴ c₄(V) = -48a₄` makes `c₄(V) = -3a₄` a unit, so `V` is nodal; `2¹² Δ(V) = Δ` drops
the level by `12`; and `2⁶ c₆(V) = -864 · 2b` makes `-c₆(V) = 27b`, so the split test is the
membership `b ∈ splitSetTwo 2`. -/
theorem multTwo_run_eq_I_of_split (hp2 : p = 2) {n : ℕ} (hn : 1 ≤ n) {a₄ b : ℤ_[p]}
    (ha₄ : IsUnit a₄) (hsplit : b ∈ splitSetTwo p)
    (hΔ : emultiplicity (p : ℤ_[p]) (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ = ((n + 12 : ℕ) : ℕ∞))
    (hΔ0 : (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ ≠ 0)
    (hV : ∃ V, TateAlgorithm.Step11.run (W := ofShortNF a₄ ((p : ℤ_[p]) * b))
      PadicInt.uniformizer_ne_zero hΔ0 = Except.ok V) :
    (TateAlgorithm.run (W := ofShortNF a₄ ((p : ℤ_[p]) * b))
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.I n ∧
      (TateAlgorithm.run (W := ofShortNF a₄ ((p : ℤ_[p]) * b))
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = n := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨V, hVe⟩ := hV
  have hVΔ0 : V.Δ ≠ 0 := TateAlgorithm.Δ_ne_zero_of_step11_ok hϖ hΔ0 hVe
  have hc₄V : V.c₄ = -3 * a₄ := by
    have h := TateAlgorithm.Step11.run_c₄ hϖ hΔ0 hVe
    rw [ofShortNF_c₄] at h
    refine mul_left_cancel₀ (pow_ne_zero 4 hϖ) ?_
    rw [h]; subst hp2; push_cast; ring
  have hc₄ : ¬ (p : ℤ_[p]) ∣ V.c₄ := by
    rw [hc₄V]
    exact fun hd => PadicInt.prime_p.not_isUnit
      (isUnit_of_dvd_unit hd ((multTwo_isUnit_neg_three hp2).mul ha₄))
  have hΔV : emultiplicity (p : ℤ_[p]) V.Δ = ((n : ℕ) : ℕ∞) := by
    have h := TateAlgorithm.Step11.run_Δ hϖ hΔ0 hVe
    have h12 : ((12 : ℕ) : ℕ∞) + emultiplicity (p : ℤ_[p]) V.Δ = ((n + 12 : ℕ) : ℕ∞) := by
      rw [← hΔ, ← h, show (p : ℤ_[p]) ^ 12 * V.Δ = (p : ℤ_[p]) ^ 12 * (1 * V.Δ) from by ring,
        PadicInt.emultiplicity_pow_mul_unit_mul 12 isUnit_one]
    obtain ⟨j, hj, hjr⟩ := ENat.exists_natCast_of_add_eq (k := 12) (n := n + 12) h12
    rw [hj, show j = n by omega]
  have hc₆V : -V.c₆ = 27 * b := by
    have h := TateAlgorithm.Step11.run_c₆ hϖ hΔ0 hVe
    rw [ofShortNF_c₆] at h
    have hV6 : V.c₆ = -27 * b := by
      refine mul_left_cancel₀ (pow_ne_zero 6 hϖ) ?_
      rw [h]; subst hp2; push_cast; ring
    rw [hV6]; ring
  have htan : TateAlgorithm.Step2.TangentSplits (p : ℤ_[p]) V :=
    (TateAlgorithm.Step2.tangentSplits_iff_isSquare_neg_c₆_of_eq_two hp2
      (dvd_Δ_of_emultiplicity_eq hn hΔV) hc₄).2
      (by rw [hc₆V]
          exact (mem_splitSetTwo_iff_isSquare hp2 (multTwo_isUnit_of_mem_splitSetTwo hsplit)).1
            hsplit)
  rw [TateAlgorithm.run_eq_of_step11_ok hϖ hΔ0 hVe hVΔ0]
  exact run_kodaira_tamagawa_of_tangentSplits hVΔ0 hc₄ hn hΔV htan

/-! ### The mass of the split level set, at every level -/

private theorem multTwo_isUnit_twentySeven (hp2 : p = 2) : IsUnit (27 : ℤ_[p]) := by
  have h := PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 27) (by rw [hp2]; norm_num)
  simpa using h

private theorem multTwo_mem_splitSetTwo_iff_zmod (hp2 : p = 2) (y : ℤ_[p]) :
    y ∈ splitSetTwo p ↔ (2 : ZMod (p ^ 4)) * (27 * PadicInt.toZModPow 4 y - 1) = 0 := by
  rw [splitSetTwo, Set.mem_ofPred_eq,
    PadicInt.pow_three_dvd_iff_two_mul_toZModPow_four_of_eq_two hp2, map_sub, map_mul, map_ofNat,
    map_one]

private theorem multTwo_zmod_split (hp2 : p = 2) :
    ∀ A S W : ZMod (p ^ 4), 27 * W = 1 → S ^ 2 = -(A ^ 3) * W →
      ((A = 5 → ((2 * (27 * S - 1) = 0 ∧ 2 * (27 * (-S) - 1) ≠ 0) ∨
            (2 * (27 * S - 1) ≠ 0 ∧ 2 * (27 * (-S) - 1) = 0))) ∧
        (A ≠ 5 → (2 * (27 * S - 1) ≠ (0 : ZMod (p ^ 4)) ∧
          2 * (27 * (-S) - 1) ≠ (0 : ZMod (p ^ 4))))) := by
  subst hp2; decide

private theorem multTwo_zmod_isSquare_gamma (hp2 : p = 2) :
    ∀ A W : ZMod (p ^ 4), 27 * W = 1 → A = 5 → 2 * (-(A ^ 3) * W - 1) = (0 : ZMod (p ^ 4)) := by
  subst hp2; decide

/-- **The exact Haar mass of the `p = 2` split locus, at every level `t`.** For `a₄` a unit,

  `μ₂(splitLevelSet 2 t a₄) = 1_{a₄ ≡ 5 mod 16}(a₄) · 2⁻¹ · (1 - 2⁻¹) · 2^{-(t+5)}`,

which is `2^{-(t+7)}` on the class `a₄ ≡ 5 mod 16` and `0` on every other unit `a₄`. -/
theorem multTwo_volume_splitLevelSet (hp2 : p = 2) (t : ℕ) {a₄ : ℤ_[p]} (ha₄ : IsUnit a₄) :
    (volume : Measure ℤ_[p]) (splitLevelSet p t a₄)
      = (minimalFstTwo p).indicator
          (fun _ => (p : ℝ≥0∞)⁻¹ * ((1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ (t + 5))) a₄ := by
  obtain ⟨w, hw⟩ := (multTwo_isUnit_twentySeven hp2).exists_right_inv
  have hwu : IsUnit w := ⟨⟨w, 27, by rw [mul_comm]; exact hw, hw⟩, rfl⟩
  have hγu : IsUnit (-(a₄ ^ 3) * w : ℤ_[p]) := ((ha₄.pow 3).neg).mul hwu
  have hW : (27 : ZMod (p ^ 4)) * PadicInt.toZModPow 4 w = 1 := by
    rw [← map_ofNat (PadicInt.toZModPow 4) 27, ← map_mul, hw, map_one]
  have hQ : ∀ y z : ℤ_[p], (p : ℤ_[p]) ^ 3 ∣ y - z →
      (y ∈ splitSetTwo p ↔ z ∈ splitSetTwo p) := fun _ _ h => mem_splitSetTwo_congr h
  rw [splitLevelSet_eq_image hp2 hw, PadicInt.measure_image_scaleByPPow,
    PadicInt.zpow_neg_natCast_eq_inv_pow_two, pow_one, show t + 6 = t + 5 + 1 by omega]
  by_cases hA : PadicInt.toZModPow 4 a₄ = (5 : ZMod (p ^ 4))
  · rw [Set.indicator_of_mem (mem_minimalFstTwo_iff.2 hA)]
    have hsq : IsSquare (-(a₄ ^ 3) * w : ℤ_[p]) := by
      rw [PadicInt.isSquare_iff_two_mul_toZModPow_four_of_eq_two hp2 hγu, map_mul, map_neg, map_pow]
      exact multTwo_zmod_isSquare_gamma hp2 _ _ hW hA
    obtain ⟨s, hs⟩ := hsq
    have hSrel : (PadicInt.toZModPow 4 s) ^ 2
        = -((PadicInt.toZModPow 4 a₄) ^ 3) * PadicInt.toZModPow 4 w := by
      have h := congrArg (PadicInt.toZModPow (p := p) 4) hs
      rw [map_mul, map_neg, map_pow, map_mul] at h
      rw [h]; ring
    have hone := (multTwo_zmod_split hp2 (PadicInt.toZModPow 4 a₄) (PadicInt.toZModPow 4 s)
      (PadicInt.toZModPow 4 w) hW hSrel).1 hA
    have hmem_s : s ∈ splitSetTwo p ↔
        (2 : ZMod (p ^ 4)) * (27 * PadicInt.toZModPow 4 s - 1) = 0 :=
      multTwo_mem_splitSetTwo_iff_zmod hp2 s
    have hmem_ns : -s ∈ splitSetTwo p ↔
        (2 : ZMod (p ^ 4)) * (27 * (-(PadicInt.toZModPow 4 s)) - 1) = 0 := by
      rw [multTwo_mem_splitSetTwo_iff_zmod hp2, map_neg]
    rw [PadicInt.volume_sqLevelSet_inter_of_unique_root_of_eq_two hp2 hγu hs hQ ?_
      (by omega : 3 ≤ t + 5)]
    rcases hone with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hmem_s.2 h1, fun hc => h2 (hmem_ns.1 hc)⟩
    · exact Or.inr ⟨fun hc => h1 (hmem_s.1 hc), hmem_ns.2 h2⟩
  · rw [Set.indicator_of_notMem (fun hc => hA (mem_minimalFstTwo_iff.1 hc))]
    by_cases hsq : IsSquare (-(a₄ ^ 3) * w : ℤ_[p])
    · obtain ⟨s, hs⟩ := hsq
      have hSrel : (PadicInt.toZModPow 4 s) ^ 2
          = -((PadicInt.toZModPow 4 a₄) ^ 3) * PadicInt.toZModPow 4 w := by
        have h := congrArg (PadicInt.toZModPow (p := p) 4) hs
        rw [map_mul, map_neg, map_pow, map_mul] at h
        rw [h]; ring
      have hnone := (multTwo_zmod_split hp2 (PadicInt.toZModPow 4 a₄) (PadicInt.toZModPow 4 s)
        (PadicInt.toZModPow 4 w) hW hSrel).2 hA
      rw [PadicInt.volume_sqLevelSet_inter_of_no_root_of_eq_two hp2 hγu hs hQ
        ⟨fun hc => hnone.1 ((multTwo_mem_splitSetTwo_iff_zmod hp2 s).1 hc),
          fun hc => hnone.2 (by
            have h := (multTwo_mem_splitSetTwo_iff_zmod hp2 (-s)).1 hc
            rwa [map_neg] at h)⟩ (by omega : 3 ≤ t + 5), mul_zero]
    · rw [PadicInt.sqLevelSet_eq_empty_of_not_isSquare_of_eq_two hp2 hγu hsq
        (by omega : 3 ≤ t + 5 + 1), Set.empty_inter, measure_empty, mul_zero]

/-! ### The locus and its mass -/

variable (p) in
/-- **The split multiplicative locus at level `n`**: `a₄ ≡ 5 mod 16`, `a₆ ≡ 6 mod 16` and
`v₂(Δ) = n + 12`. The second congruence is the split test. -/
noncomputable def multSplitLocusTwo (n : ℕ) : Set (ℤ_[p] × ℤ_[p]) :=
  (Prod.fst ⁻¹' (PadicInt.toZModPow 4 ⁻¹' {(5 : ZMod (p ^ 4))})) ∩
    (Prod.snd ⁻¹' (PadicInt.toZModPow 4 ⁻¹' {(6 : ZMod (p ^ 4))})) ∩
    ((fun x : ℤ_[p] × ℤ_[p] => (ofShortNF x.1 x.2).Δ) ⁻¹'
      {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) y = ((n + 12 : ℕ) : ℕ∞)})

/-- Membership in `multSplitLocusTwo p n` unfolds to its three defining conditions. -/
theorem mem_multSplitLocusTwo_iff {n : ℕ} {x : ℤ_[p] × ℤ_[p]} :
    x ∈ multSplitLocusTwo p n ↔ PadicInt.toZModPow 4 x.1 = (5 : ZMod (p ^ 4)) ∧
      PadicInt.toZModPow 4 x.2 = (6 : ZMod (p ^ 4)) ∧
      emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = ((n + 12 : ℕ) : ℕ∞) :=
  ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- The split multiplicative locus `multSplitLocusTwo p n` is measurable. -/
theorem measurableSet_multSplitLocusTwo (n : ℕ) : MeasurableSet (multSplitLocusTwo p n) :=
  (((PadicInt.measurableSet_preimage_toZModPow 4 _).preimage measurable_fst).inter
      ((PadicInt.measurableSet_preimage_toZModPow 4 _).preimage measurable_snd)).inter
    ((PadicInt.measurableSet_setOf_emultiplicity_eq (n + 12)).preimage
      continuous_shortNF_Δ.measurable)

/-- The `a₆`-slice of the locus over an `a₄` in `minimalFstTwo 2` is the split level set. -/
theorem multTwo_slice_eq (hp2 : p = 2) (n : ℕ) {a₄ : ℤ_[p]}
    (ha₄ : PadicInt.toZModPow 4 a₄ = (5 : ZMod (p ^ 4))) :
    Prod.mk a₄ ⁻¹' multSplitLocusTwo p n = splitLevelSet p n a₄ := by
  ext a₆
  rw [Set.mem_preimage, mem_multSplitLocusTwo_iff, splitLevelSet, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨(multTwo_toZModPow_four_eq_six_iff hp2).1 h.2.1, h.2.2⟩,
    fun h => ⟨ha₄, (multTwo_toZModPow_four_eq_six_iff hp2).2 h.1, h.2⟩⟩

/-- Off `minimalFstTwo 2` the locus has empty `a₆`-slice. -/
theorem multTwo_slice_eq_empty (n : ℕ) {a₄ : ℤ_[p]}
    (ha₄ : PadicInt.toZModPow 4 a₄ ≠ (5 : ZMod (p ^ 4))) :
    Prod.mk a₄ ⁻¹' multSplitLocusTwo p n = (∅ : Set ℤ_[p]) :=
  Set.eq_empty_iff_forall_notMem.2 fun _ hx => ha₄ (mem_multSplitLocusTwo_iff.1 hx).1

/-- **The mass of the split multiplicative locus is `2^{-(n+11)}`.** The `a₄`-class weighs `2⁻⁴`,
the rescaling `a₆ = 2b` weighs `2⁻¹`, the surviving shell weighs `(1 - 2⁻¹)` and its level weighs
`2^{-(n+5)}`. -/
theorem volume_multSplitLocusTwo (hp2 : p = 2) (n : ℕ) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (multSplitLocusTwo p n)
      = (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ (n + 10) := by
  have hslice : ∀ a₄ : ℤ_[p], (volume : Measure ℤ_[p]) (Prod.mk a₄ ⁻¹' multSplitLocusTwo p n)
      = (minimalFstTwo p).indicator
          (fun _ => (p : ℝ≥0∞)⁻¹ * ((1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ (n + 5))) a₄ := by
    intro a₄
    by_cases ha₄ : PadicInt.toZModPow 4 a₄ = (5 : ZMod (p ^ 4))
    · rw [multTwo_slice_eq hp2 n ha₄,
        multTwo_volume_splitLevelSet hp2 n (isUnit_of_mem_minimalFstTwo hp2
          (mem_minimalFstTwo_iff.2 ha₄))]
    · rw [multTwo_slice_eq_empty n ha₄, measure_empty,
        Set.indicator_of_notMem (fun hc => ha₄ (mem_minimalFstTwo_iff.1 hc))]
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_multSplitLocusTwo n),
    lintegral_congr hslice, lintegral_indicator_const measurableSet_minimalFstTwo,
    volume_minimalFstTwo, ENNReal.inv_pow, show n + 10 = 4 + (1 + (n + 5)) by omega,
    pow_add, pow_add]
  ring

/-! ### Tate's algorithm on the locus -/

/-- **On the split multiplicative locus at level `n ≥ 1` Tate's algorithm answers `(Iₙ, n)`.** -/
theorem multTwo_run_eq_I_of_mem (hp2 : p = 2) {n : ℕ} (hn : 1 ≤ n) {a₄ a₆ : ℤ_[p]}
    (hx : ((a₄, a₆) : ℤ_[p] × ℤ_[p]) ∈ multSplitLocusTwo p n)
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.I n ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = n := by
  have hπ : (p : ℤ_[p]) = 2 := by subst hp2; norm_num
  obtain ⟨ha, hsix, hd⟩ := mem_multSplitLocusTwo_iff.1 hx
  obtain ⟨b, hb, hsplit⟩ := (multTwo_toZModPow_four_eq_six_iff hp2).1 hsix
  subst hb
  have ha₄u : IsUnit a₄ := isUnit_of_mem_minimalFstTwo hp2 (mem_minimalFstTwo_iff.2 ha)
  have h12 : (p : ℤ_[p]) ^ 12 ∣ (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ :=
    pow_dvd_of_le_emultiplicity (by rw [hd]; exact_mod_cast (by omega : 12 ≤ n + 12))
  obtain ⟨α, k, hα, hk⟩ := multTwo_exists_params_of_dvd_twelve hp2 (by rw [hπ]) hsplit h12
  exact multTwo_run_eq_I_of_split hp2 hn ha₄u hsplit hd hΔ0
    (TateAlgorithm.Step11.run_eq_ok_of_params_two hp2 hΔ0 (b := b) (α := α) (k := k)
      (by rw [hπ]) ha₄u hα hk)

/-- The short model is nonsingular on the locus: `v₂(Δ) = n + 12` is finite. -/
theorem multTwo_Δ_ne_zero_of_mem {n : ℕ} {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ multSplitLocusTwo p n) :
    (ofShortNF x.1 x.2).Δ ≠ 0 := by
  intro h0
  have hd := (mem_multSplitLocusTwo_iff.1 hx).2.2
  rw [h0, emultiplicity_zero_right] at hd
  exact (ENat.natCast_ne_top (n + 12)) hd.symm

/-- **On the split multiplicative locus at level `n ≥ 1` Tate's algorithm answers `(Iₙ, n)`**,
stated for a point of the plane. -/
theorem multTwo_run_eq_I_of_mem' (hp2 : p = 2) {n : ℕ} (hn : 1 ≤ n) {x : ℤ_[p] × ℤ_[p]}
    (hx : x ∈ multSplitLocusTwo p n) (hΔ0 : (ofShortNF x.1 x.2).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.I n ∧
      (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = n :=
  multTwo_run_eq_I_of_mem hp2 hn hx hΔ0

/-- **The split multiplicative locus at level `n` lies in the strata over `t = n`.** -/
theorem multSplitLocusTwo_subset_iUnion_stratFibre (hp2 : p = 2) {n : ℕ} (hn : 1 ≤ n) :
    multSplitLocusTwo p n ⊆ ⋃ κ : KodairaSymbol, stratFibre p (κ, n) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := multTwo_Δ_ne_zero_of_mem hx
  have hUp : x ∈ nonsingularLocus p := hΔ
  obtain ⟨hκ, ht⟩ := multTwo_run_eq_I_of_mem' hp2 hn hx hΔ
  exact Set.mem_iUnion.2 ⟨KodairaSymbol.I n,
    (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ ht)⟩

/-- **The locus lies in the minimal part of the `t = n` row**: `a₄` is a unit on it, and a dilate
needs `2⁴ ∣ a₄`. -/
theorem multSplitLocusTwo_subset_headMinimal (hp2 : p = 2) {n : ℕ} (hn : 1 ≤ n) :
    multSplitLocusTwo p n ⊆ (⋃ κ : KodairaSymbol, stratFibre p (κ, n)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) := by
  intro x hx
  refine ⟨multSplitLocusTwo_subset_iUnion_stratFibre hp2 hn hx, ?_⟩
  exact notMem_range_of_isUnit_fst_two (isUnit_of_mem_minimalFstTwo hp2
    (mem_minimalFstTwo_iff.2 (mem_multSplitLocusTwo_iff.1 hx).1))

/-! ### The mass of the split locus at `p = 2`, evaluated -/

/-- `1 - 2⁻¹ = 2⁻¹` in `ℝ≥0∞`. -/
private theorem multTwo_one_sub_inv (hp2 : p = 2) :
    (1 : ℝ≥0∞) - (p : ℝ≥0∞)⁻¹ = (p : ℝ≥0∞)⁻¹ := by
  subst hp2
  refine ENNReal.sub_eq_of_eq_add (by simp) ?_
  rw [show (((2 : ℕ) : ℝ≥0∞))⁻¹ + (((2 : ℕ) : ℝ≥0∞))⁻¹ = 2 * (((2 : ℕ) : ℝ≥0∞))⁻¹ from by ring]
  norm_num
  exact (ENNReal.mul_inv_cancel (by norm_num) (by norm_num)).symm

/-- **The mass of the split multiplicative locus, evaluated:** `2^{-(n+11)}`. -/
theorem volume_multSplitLocusTwo_at_two (n : ℕ) :
    (volume : Measure (ℤ_[2] × ℤ_[2])) (multSplitLocusTwo 2 n) = ((2 : ℝ≥0∞)⁻¹) ^ (n + 11) := by
  have h2 : ((2 : ℕ) : ℝ≥0∞) = 2 := by norm_num
  have hpow : ((2 : ℝ≥0∞)⁻¹) ^ (n + 11) = (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ (n + 10) := by
    rw [show n + 11 = (n + 10) + 1 from by omega, pow_succ]; ring
  rw [volume_multSplitLocusTwo (p := 2) rfl n, multTwo_one_sub_inv (p := 2) rfl, h2, hpow]

/-! ### The non-split half: its congruence, its parameters, and its Tamagawa number -/

variable (p) in
/-- **The non-split test at `p = 2`**: `27b ≡ 5 mod 8`, equivalently `b ≡ 7 mod 8`. On the
multiplicative shell `b ≡ 3 mod 4`, so this is exactly the complement of `splitSetTwo`, and
`-c₆(V) = 27b` is then a non-square. -/
def multNonSplitSetTwo : Set ℤ_[p] := {b : ℤ_[p] | (p : ℤ_[p]) ^ 3 ∣ 27 * b - 5}

/-- `multNonSplitSetTwo p` is a union of residue classes modulo `p³`. -/
theorem multTwo_mem_nonSplit_congr {y z : ℤ_[p]} (h : (p : ℤ_[p]) ^ 3 ∣ y - z) :
    y ∈ multNonSplitSetTwo p ↔ z ∈ multNonSplitSetTwo p := by
  obtain ⟨c, hc⟩ := h
  exact dvd_iff_dvd_of_dvd_sub ⟨27 * c, by linear_combination 27 * hc⟩

/-- **`a₆ ≡ 14 mod 16` is exactly `a₆ = 2b` with `b ≡ 7 mod 8`.** -/
theorem multTwo_toZModPow_four_eq_fourteen_iff (hp2 : p = 2) {a₆ : ℤ_[p]} :
    PadicInt.toZModPow 4 a₆ = (14 : ZMod (p ^ 4)) ↔
      ∃ b, a₆ = (p : ℤ_[p]) * b ∧ b ∈ multNonSplitSetTwo p := by
  have hπ : (p : ℤ_[p]) = 2 := by subst hp2; norm_num
  constructor
  · intro h
    obtain ⟨c, hc⟩ : (p : ℤ_[p]) ^ 4 ∣ a₆ - 14 := by
      rw [TateAlgorithm.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_ofNat, h, sub_self]
    rw [hπ] at hc
    exact ⟨7 + 8 * c, by rw [hπ]; linear_combination hc, ⟨23 + 27 * c, by rw [hπ]; ring⟩⟩
  · rintro ⟨b, rfl, hb⟩
    obtain ⟨u, hu⟩ : (p : ℤ_[p]) ^ 3 ∣ 27 * b - 5 := hb
    obtain ⟨w, hw⟩ := multTwo_exists_inv_twentySeven (p := p) hp2
    rw [hπ] at hu
    obtain ⟨c, hc⟩ : ∃ c : ℤ_[p], b - 7 = 8 * c :=
      ⟨w * (u - 23), by linear_combination w * hu + (7 - b) * hw⟩
    have hd : (p : ℤ_[p]) ^ 4 ∣ (p : ℤ_[p]) * b - 14 := ⟨c, by rw [hπ]; linear_combination 2 * hc⟩
    rwa [TateAlgorithm.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_ofNat, sub_eq_zero] at hd

/-- A member of `multNonSplitSetTwo 2` is a unit and is not in `splitSetTwo 2`. -/
theorem multTwo_isUnit_and_notMem_split_of_nonsplit (hp2 : p = 2) {b : ℤ_[p]}
    (hb : b ∈ multNonSplitSetTwo p) : IsUnit b ∧ b ∉ splitSetTwo p := by
  have hπ : (p : ℤ_[p]) = 2 := by subst hp2; norm_num
  have h4 : (4 : ℤ_[p]) ≠ 0 := by
    rw [show (4 : ℤ_[p]) = (p : ℤ_[p]) ^ 2 from by rw [hπ]; norm_num]
    exact pow_ne_zero 2 PadicInt.uniformizer_ne_zero
  obtain ⟨u, hu⟩ : (p : ℤ_[p]) ^ 3 ∣ 27 * b - 5 := hb
  rw [hπ] at hu
  constructor
  · refine not_not.1 fun hnu => ?_
    obtain ⟨c, hc⟩ := PadicInt.dvd_iff_not_isUnit.2 hnu
    rw [hπ] at hc
    exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_one (a := (p : ℤ_[p]))
      ⟨27 * c - 4 * u - 2, by rw [hπ]; linear_combination -hu + 27 * hc⟩)
  · intro hs
    obtain ⟨y, hy⟩ : (p : ℤ_[p]) ^ 3 ∣ 27 * b - 1 := hs
    rw [hπ] at hy
    refine PadicInt.prime_p.not_isUnit (isUnit_of_dvd_one (a := (p : ℤ_[p])) ⟨y - u, ?_⟩)
    refine mul_left_cancel₀ h4 ?_
    rw [hπ]
    linear_combination hy - hu

private theorem multTwo_zmod_a₄_of_cube_nonsplit (hp2 : p = 2) :
    ∀ A : ZMod (p ^ 4), A ^ 3 + 11 = 0 → A - 13 = 0 := by
  subst hp2; decide

private theorem multTwo_zmod_beta_nonsplit (hp2 : p = 2) :
    ∀ A B : ZMod (p ^ 2),
      220 + 507 * A + 624 * A ^ 2 + 256 * A ^ 3 + 189 * B + 108 * B ^ 2 = 0 → B - A = 0 := by
  subst hp2; decide

/-- **The non-split locus at level `2 ^ 12`, parametrised**: `a₄ = 13 + 16α`,
`b = 7 + 8α + 32k`. -/
theorem multTwo_exists_params_nonsplit_of_dvd_twelve (hp2 : p = 2) {a₄ a₆ b : ℤ_[p]}
    (ha₆ : a₆ = 2 * b) (hns : b ∈ multNonSplitSetTwo p)
    (hΔ : (p : ℤ_[p]) ^ 12 ∣ (ofShortNF a₄ a₆).Δ) :
    ∃ α k : ℤ_[p], a₄ = 13 + 16 * α ∧ b = 7 + 8 * α + 32 * k := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hπ : (p : ℤ_[p]) = 2 := by subst hp2; norm_num
  obtain ⟨w, hw⟩ := multTwo_exists_inv_twentySeven (p := p) hp2
  obtain ⟨u, hu⟩ : (p : ℤ_[p]) ^ 3 ∣ 27 * b - 5 := hns
  rw [hπ] at hu
  obtain ⟨β, hβ⟩ : ∃ β : ℤ_[p], b = 7 + 8 * β :=
    ⟨w * (u - 23), by linear_combination w * hu + (7 - b) * hw⟩
  obtain ⟨γ, hγ⟩ : (p : ℤ_[p]) ^ 6 ∣ a₄ ^ 3 + 27 * b ^ 2 := by
    have hkey : (ofShortNF a₄ a₆).Δ = (p : ℤ_[p]) ^ 6 * (-(a₄ ^ 3 + 27 * b ^ 2)) := by
      rw [ofShortNF_Δ, ha₆, hπ]; ring
    rw [hkey, show (12 : ℕ) = 6 + 6 from rfl, pow_add,
      mul_dvd_mul_iff_left (pow_ne_zero 6 hϖ)] at hΔ
    exact dvd_neg.1 hΔ
  rw [hπ] at hγ
  obtain ⟨α, hα⟩ : (p : ℤ_[p]) ^ 4 ∣ a₄ - 13 := by
    have h16 : (p : ℤ_[p]) ^ 4 ∣ a₄ ^ 3 + 11 := by
      refine ⟨4 * γ - (82 + 189 * β + 108 * β ^ 2), ?_⟩
      rw [hπ, hβ] at *
      linear_combination hγ
    rw [TateAlgorithm.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_ofNat]
    refine multTwo_zmod_a₄_of_cube_nonsplit hp2 _ ?_
    have hz := (TateAlgorithm.pow_dvd_iff_toZModPow_eq_zero 4 _).1 h16
    rwa [map_add, map_pow, map_ofNat] at hz
  rw [hπ] at hα
  have ha₄ : a₄ = 13 + 16 * α := by linear_combination hα
  have h16ne : (16 : ℤ_[p]) ≠ 0 := by
    rw [show (16 : ℤ_[p]) = (p : ℤ_[p]) ^ 4 from by rw [hπ]; norm_num]
    exact pow_ne_zero 4 hϖ
  have hE : (220 : ℤ_[p]) + 507 * α + 624 * α ^ 2 + 256 * α ^ 3 + 189 * β + 108 * β ^ 2
      = 4 * γ := by
    refine mul_left_cancel₀ h16ne ?_
    rw [ha₄, hβ] at hγ
    linear_combination hγ
  obtain ⟨k, hk⟩ : (p : ℤ_[p]) ^ 2 ∣ β - α := by
    rw [TateAlgorithm.pow_dvd_iff_toZModPow_eq_zero, map_sub]
    refine multTwo_zmod_beta_nonsplit hp2 _ _ ?_
    have hd : (p : ℤ_[p]) ^ 2 ∣ 220 + 507 * α + 624 * α ^ 2 + 256 * α ^ 3 + 189 * β
        + 108 * β ^ 2 := ⟨γ, by rw [hπ]; linear_combination hE⟩
    have hz := (TateAlgorithm.pow_dvd_iff_toZModPow_eq_zero 2 _).1 hd
    rwa [map_add, map_add, map_add, map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_mul,
      map_pow, map_pow, map_pow, map_ofNat, map_ofNat, map_ofNat, map_ofNat, map_ofNat,
      map_ofNat] at hz
  rw [hπ] at hk
  exact ⟨α, k, ha₄, by rw [hβ]; linear_combination 8 * hk⟩

/-! ### Steps 1–10 on the non-split family -/

namespace TateAlgorithm

private theorem multTwo_div_eq_of_eq_mul {x a : ℤ_[p]} (h : x = (p : ℤ_[p]) * a) :
    div x (p : ℤ_[p]) = a := by
  subst h
  exact mul_left_cancel₀ PadicInt.uniformizer_ne_zero
    (CommRing.mul_div PadicInt.uniformizer_ne_zero (Dvd.intro a rfl))

private theorem multTwo_mod_eq_mod_of_dvd_sub {x y : ℤ_[p]} (h : (p : ℤ_[p]) ∣ x - y) :
    mod (p : ℤ_[p]) x = mod (p : ℤ_[p]) y := by
  rw [← sub_eq_zero, ← map_sub, mod_eq_zero]; exact h

/-- **Steps 1–10 of Tate's algorithm cannot answer on a short model over `ℤ_2` with `a₄ = 13 + 16α`
and `a₆ = 2(7 + 8α + 32k)`, so Step 11 fires.** No hypothesis on `v₂(Δ)` is needed. -/
theorem Step11.run_eq_ok_of_params_nonsplit_two (hp2 : p = 2) {a₄ a₆ b α k : ℤ_[p]}
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) (ha₆' : a₆ = 2 * b) (ha₄u : IsUnit a₄)
    (ha₄ : a₄ = 13 + 16 * α) (hb : b = 7 + 8 * α + 32 * k) :
    ∃ V, Step11.run PadicInt.uniformizer_ne_zero hΔ0 = Except.ok V := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have hπ : (p : ℤ_[p]) = 2 := by subst hp2; norm_num
  have hΔd : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ :=
    ⟨-32 * (a₄ ^ 3 + 27 * b ^ 2), by rw [ofShortNF_Δ, ha₆', hπ]; ring⟩
  have hc₄ : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).c₄ :=
    dvd_ofShortNF_c₄_of_eq_two_or_three (Or.inl hp2) a₄ a₆
  have h2run : Step2.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok (Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)) :=
    Step2.run_eq_ok_of_dvd_c₄ hΔd hc₄
  obtain ⟨r, t, hV1⟩ : ∃ r t : ℤ_[p], Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆ := ⟨_, _, dite_eq_left hΔd⟩
  have hval2 := Step2.hasValuation_translate hΔd
  rw [hV1] at h2run hval2
  have hva₄ : (p : ℤ_[p]) ∣ a₄ + 3 * r ^ 2 - 2 * 0 * t := by
    have h := hval2.a₄; rwa [smul_ofShortNF_a₄, pow_one] at h
  have hva₆ : (p : ℤ_[p]) ∣ a₆ + r * a₄ + r ^ 3 - t ^ 2 := by
    have h := hval2.a₆; rwa [smul_ofShortNF_a₆, pow_one] at h
  obtain ⟨ρ, hr⟩ : ∃ ρ : ℤ_[p], r = 1 + 2 * ρ := by
    obtain ⟨y, hy | hy⟩ := exists_even_or_odd_two hp2 hπ r
    · exfalso
      obtain ⟨c, hc⟩ := hva₄
      rw [hy, hπ] at hc
      exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_unit
        ⟨c - 6 * y ^ 2, by rw [hπ]; linear_combination hc⟩ ha₄u)
    · exact ⟨y, hy⟩
  obtain ⟨m, hm⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ρ
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[p], t = 2 * τ := by
    have h2 : (p : ℤ_[p]) ∣ a₆ + r * a₄ + r ^ 3 :=
      ⟨b + 7 + 8 * α + 16 * ρ + 16 * α * ρ + 6 * ρ ^ 2 + 4 * ρ ^ 3, by
        rw [hπ, ha₆', ha₄, hr]; ring⟩
    have h3 : (p : ℤ_[p]) ∣ t ^ 2 := by
      have h := dvd_sub h2 hva₆
      rwa [show a₆ + r * a₄ + r ^ 3 - (a₆ + r * a₄ + r ^ 3 - t ^ 2) = t ^ 2 from by ring] at h
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow h3
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨mτ, hmτ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[p], x = 2 + 2 * α + 3 * m := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[p],
      x = 7 + 8 * α + 16 * k + 7 * ρ + 8 * α * ρ + 2 * m + 4 * ρ * m - τ ^ 2 := ⟨_, rfl⟩
  have hV1a₁ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₁ = 0 := by
    rw [smul_ofShortNF_a₁]; ring
  have hV1a₂ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 * r := by
    rw [smul_ofShortNF_a₂]; ring
  have hV1a₃ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₃ = (p : ℤ_[p]) ^ 2 * τ := by
    rw [smul_ofShortNF_a₃, hπ, ht]; ring
  have hV1a₄ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₄ = (p : ℤ_[p]) ^ 3 * Q₄ := by
    rw [smul_ofShortNF_a₄, hπ, ha₄, hr, hQ₄]; linear_combination 12 * hm
  have hV1a₆ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ 2 * Q₆ := by
    rw [smul_ofShortNF_a₆, hπ, ha₆', hb, ha₄, hr, ht, hQ₆]; linear_combination (4 + 8 * ρ) * hm
  have h3run : Step3.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step3.run.eq_def, h2run]
    simp only [except_ok_bind]
    exact ite_eq_left ⟨Q₆, hV1a₆⟩
  have h4run : Step4.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step4.run.eq_def, h3run]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨6 * r * Q₆ + 6 * r * τ ^ 2 - 8 * Q₄ ^ 2, ?_⟩
    rw [WeierstrassCurve.b₈, hV1a₁, hV1a₂, hV1a₃, hV1a₄, hV1a₆, hπ]; ring
  have h5run : Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by
    rw [Step5.run.eq_def, h4run]
    simp only [except_ok_bind]
    refine ite_eq_left ⟨2 * τ ^ 2 + 2 * Q₆, ?_⟩
    rw [WeierstrassCurve.b₆, hV1a₃, hV1a₆, hπ]; ring
  obtain ⟨s, hsdef⟩ : ∃ x : ℤ_[p],
      x = Step6.s (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨t₆, ht₆def⟩ : ∃ x : ℤ_[p],
      x = Step6.t (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨σ, hs2⟩ : ∃ σ : ℤ_[p], s = 1 + 2 * σ := by
    have h : (p : ℤ_[p]) ∣ s - 3 * r := by
      rw [← mod_eq_zero, map_sub, hsdef, Step6.mod_s_two hp2, hV1a₂, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ, hr] at hj
    exact ⟨1 + 3 * ρ + j, by linear_combination hj⟩
  obtain ⟨mσ, hmσ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ σ
  obtain ⟨θ, hθ⟩ : ∃ θ : ℤ_[p],
      (p : ℤ_[p]) * t₆ + t = (p : ℤ_[p]) * (1 + ρ + 2 * θ) := by
    have h : (p : ℤ_[p]) ∣ t₆ - Q₆ := by
      rw [← mod_eq_zero, map_sub, ht₆def, Step6.mod_t_two hp2,
        div_eq_of_eq_pow_mul_two hV1a₆, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ, hQ₆] at hj
    refine ⟨3 + 4 * α + 8 * k + 3 * ρ + 4 * α * ρ + m + 2 * ρ * m + τ - mτ + j, ?_⟩
    rw [hπ, ht]
    linear_combination 2 * hj - 2 * hmτ
  obtain ⟨T₂, hT₂⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) * t₆ + t := ⟨_, rfl⟩
  have hT₂v : T₂ = (p : ℤ_[p]) * (1 + ρ + 2 * θ) := by rw [hT₂, hθ]
  have hV2 : Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ := by
    have h : Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 s ((p : ℤ_[p]) * t₆))
          • ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by rw [hsdef, ht₆def]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hT₂]; ring)
  obtain ⟨X₂, hX₂⟩ : ∃ x : ℤ_[p], x = 1 + 3 * ρ - 4 * mσ := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ x : ℤ_[p], x = 2 * Q₄ - (1 + 2 * σ) * (1 + ρ + 2 * θ) := ⟨_, rfl⟩
  obtain ⟨X₆, hX₆⟩ : ∃ x : ℤ_[p], x = 3 + 4 * α + 8 * k + 3 * ρ + 4 * α * ρ + 2 * ρ * m
      - 2 * θ - 2 * ρ * θ - 2 * θ ^ 2 := ⟨_, rfl⟩
  have hV2a₂ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂ = (p : ℤ_[p]) * X₂ := by
    rw [smul_ofShortNF_a₂, hπ, hr, hs2, hX₂]; linear_combination -4 * hmσ
  have hV2a₄ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄ = (p : ℤ_[p]) ^ 2 * X₄ := by
    rw [smul_ofShortNF_a₄, hT₂v, hπ, ha₄, hr, hs2, hX₄, hQ₄]; linear_combination 12 * hm
  have hV2a₆ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ 3 * X₆ := by
    rw [smul_ofShortNF_a₆, hT₂v, hπ, ha₆', hb, ha₄, hr, hX₆]; linear_combination 8 * ρ * hm
  have hcb : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).b
      = mod (p : ℤ_[p]) (1 + ρ) := by
    change mod (p : ℤ_[p]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂)
      (p : ℤ_[p])) = _
    rw [multTwo_div_eq_of_eq_mul hV2a₂]
    exact multTwo_mod_eq_mod_of_dvd_sub ⟨ρ - 2 * mσ, by rw [hπ, hX₂]; ring⟩
  have hcc : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c
      = mod (p : ℤ_[p]) (1 + ρ) := by
    change mod (p : ℤ_[p]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄)
      ((p : ℤ_[p]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two hV2a₄]
    exact multTwo_mod_eq_mod_of_dvd_sub
      ⟨1 + 2 * α + 3 * m - ρ - θ - σ * (1 + ρ + 2 * θ), by rw [hπ, hX₄, hQ₄]; ring⟩
  have hcd : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d
      = mod (p : ℤ_[p]) (1 + ρ) := by
    change mod (p : ℤ_[p]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆)
      ((p : ℤ_[p]) ^ 3)) = _
    rw [div_eq_of_eq_pow_mul_two hV2a₆]
    exact multTwo_mod_eq_mod_of_dvd_sub
      ⟨1 + 2 * α + 4 * k + ρ + 2 * α * ρ + ρ * m - θ - ρ * θ - θ ^ 2, by rw [hπ, hX₆]; ring⟩
  have hdouble := hasDoubleRoot_of_eq_two hp2 (by simp [cubic]) hcb hcc hcd
  have htriple := hasTripleRoot_of_eq_two hp2 hcb hcc
  have h6run : Step6.run (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = Except.ok ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by
    rw [Step6.run.eq_def, h5run]
    simp only [except_ok_bind]
    rw [hV2]
    exact ite_eq_left (by rw [← hV2] at hdouble ⊢; exact hdouble)
  have h7run : Step7.run hϖ hΔ0
      = Except.ok ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by
    rw [Step7.run]
    split
    · next out heq => rw [h6run] at heq; exact absurd heq (by simp)
    · next W' heq =>
        obtain rfl : W' = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ :=
          Except.ok.inj (heq.symm.trans h6run)
        exact dite_eq_left htriple
  obtain ⟨r₈, hr₈def⟩ : ∃ x : ℤ_[p],
      x = Step8.r (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℤ_[p], r₈ = 1 + ρ + 2 * ψ := by
    have h : (p : ℤ_[p]) ∣ r₈ - X₂ := by
      rw [← mod_eq_zero, map_sub, hr₈def, Step8.mod_r_two hp2,
        multTwo_div_eq_of_eq_mul hV2a₂, sub_self]
    obtain ⟨j, hj⟩ := h
    rw [hπ, hX₂] at hj
    exact ⟨ρ - 2 * mσ + j, by linear_combination hj⟩
  obtain ⟨R₃, hR₃⟩ : ∃ x : ℤ_[p], x = -1 - 4 * ψ := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ x : ℤ_[p], x = θ - ψ - σ * (1 + ρ) - 2 * σ * ψ := ⟨_, rfl⟩
  obtain ⟨T₃, hT₃⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 2 * v := ⟨_, rfl⟩
  have hV3 : Step8.translate (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆ := by
    have h : Step8.translate (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 (-(p : ℤ_[p]) * r₈) 0 0)
          • ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by rw [hr₈def]
    rw [h]
    refine smul_smul_eq _ ?_ (by ring) ?_
    · rw [hR₃, hπ, hψ, hr]; ring
    · rw [hT₃, hT₂v, hπ, hψ, hs2, hv]; ring
  obtain ⟨E, hE⟩ : ∃ x : ℤ_[p], x = 4 * k - 4 * ψ - 4 * α * ψ - 3 * ψ ^ 2 - 4 * ψ ^ 3
      - v ^ 2 := ⟨_, rfl⟩
  have hV3a₃ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃ = (p : ℤ_[p]) ^ 3 * v := by
    rw [smul_ofShortNF_a₃, hT₃, hπ]; ring
  have hV3a₆ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ 4 * E := by
    rw [smul_ofShortNF_a₆, hR₃, hT₃, hπ, ha₆', hb, ha₄, hE]; ring
  have hqc : (quadratic (p : ℤ_[p]) ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).c
      = 0 := by
    change mod (p : ℤ_[p]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃)
      ((p : ℤ_[p]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two (show ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃
      = (p : ℤ_[p]) ^ 2 * ((p : ℤ_[p]) * v) from by rw [hV3a₃]; ring), map_mul, mod_self, zero_mul]
  have hq := quadratic_hasDoubleRoot_of_eq_two hp2 (by simp [quadratic])
    (by simp [quadratic]) hqc
  have h8run : Step8.run hϖ hΔ0
      = Except.ok ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) := by
    rw [Step8.run.eq_def, h7run]
    simp only [except_ok_bind]
    rw [hV3]
    exact ite_eq_left hq
  obtain ⟨mψ, hmψ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ψ
  obtain ⟨mv, hmv⟩ := exists_sq_add_self_eq_two_mul hp2 hπ v
  obtain ⟨tY, htYdef⟩ : ∃ x : ℤ_[p],
      x = Step7.tY (p : ℤ_[p]) ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ l : ℤ_[p], v + tY = ψ + 2 * l := by
    have h : (p : ℤ_[p]) ∣ tY + E := by
      rw [← mod_eq_zero, map_add, htYdef,
        (Step7.mod_tY_two hp2 ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2 :
          mod (p : ℤ_[p])
              (Step7.tY (p : ℤ_[p]) ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2)
            = - mod (p : ℤ_[p]) (div (((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆)
                ((p : ℤ_[p]) ^ 4))),
        div_eq_of_eq_pow_mul_two hV3a₆, neg_add_cancel]
    obtain ⟨j, hj⟩ := h
    rw [hπ, hE] at hj
    refine ⟨mv + 3 * mψ - 2 * k + 2 * α * ψ + 2 * ψ ^ 3 + j, ?_⟩
    linear_combination hj + hmv + 3 * hmψ
  obtain ⟨T₄, hT₄⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 2 * (ψ + 2 * lam) := ⟨_, rfl⟩
  have hV4 : Step9.translate (p : ℤ_[p]) ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆ := by
    have h : Step9.translate (p : ℤ_[p]) ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 0 ((p : ℤ_[p]) ^ 2 * tY))
          • ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) := by rw [htYdef]
    rw [h]
    refine smul_smul_eq _ (by ring) (by ring) ?_
    rw [hT₄, hT₃]
    linear_combination -(p : ℤ_[p]) ^ 2 * hlam
  have hV4a₄ : ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆).a₄
      = (p : ℤ_[p]) ^ 4 * (1 + α + ψ + 3 * ψ ^ 2 - lam - σ * ψ - 2 * σ * lam) := by
    rw [smul_ofShortNF_a₄, hR₃, hT₄, hπ, ha₄, hs2]; ring
  have hV4a₆ : ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ 6 * (k - ψ - α * ψ - ψ ^ 2 - ψ ^ 3 - lam * ψ - lam ^ 2) := by
    rw [smul_ofShortNF_a₆, hR₃, hT₄, hπ, ha₆', hb, ha₄]; ring
  have h9run : Step9.run hϖ hΔ0
      = Except.ok ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆) := by
    rw [Step9.run.eq_def, h8run]
    simp only [except_ok_bind]
    rw [hV4]
    exact ite_eq_left ⟨_, hV4a₄⟩
  have h10run : Step10.run hϖ hΔ0
      = Except.ok ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆) := by
    rw [Step10.run.eq_def, h9run]
    simp only [except_ok_bind]
    exact ite_eq_left ⟨_, hV4a₆⟩
  exact ⟨Step11.translate (p : ℤ_[p]) ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆), by
    rw [Step11.run.eq_def, h10run]; rfl⟩

end TateAlgorithm

/-! ### The second run on the non-split half -/

open scoped Classical in
/-- **The non-split multiplicative datum at `p = 2`, for every `n ≥ 1`**: the Kodaira symbol is
`Iₙ` and the Tamagawa number is `1` for odd `n` and `2` for even `n`. On the descended curve
`c₄(V) = -3a₄` is a unit, `v₂(Δ(V)) = n` and `-c₆(V) = 27b`, and `27b ≡ 5 mod 8` is a non-square,
so the tangent quadratic of Step 2 does not split. -/
theorem multTwo_run_eq_I_of_nonsplit (hp2 : p = 2) {n : ℕ} (hn : 1 ≤ n) {a₄ b : ℤ_[p]}
    (ha₄ : IsUnit a₄) (hns : b ∈ multNonSplitSetTwo p)
    (hΔ : emultiplicity (p : ℤ_[p]) (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ = ((n + 12 : ℕ) : ℕ∞))
    (hΔ0 : (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ ≠ 0)
    (hV : ∃ V, TateAlgorithm.Step11.run (W := ofShortNF a₄ ((p : ℤ_[p]) * b))
      PadicInt.uniformizer_ne_zero hΔ0 = Except.ok V) :
    (TateAlgorithm.run (W := ofShortNF a₄ ((p : ℤ_[p]) * b))
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.I n ∧
      (TateAlgorithm.run (W := ofShortNF a₄ ((p : ℤ_[p]) * b))
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = (if Odd n then 1 else 2) := by
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  obtain ⟨V, hVe⟩ := hV
  have hVΔ0 : V.Δ ≠ 0 := TateAlgorithm.Δ_ne_zero_of_step11_ok hϖ hΔ0 hVe
  have hc₄V : V.c₄ = -3 * a₄ := by
    have h := TateAlgorithm.Step11.run_c₄ hϖ hΔ0 hVe
    rw [ofShortNF_c₄] at h
    refine mul_left_cancel₀ (pow_ne_zero 4 hϖ) ?_
    rw [h]; subst hp2; push_cast; ring
  have hc₄ : ¬ (p : ℤ_[p]) ∣ V.c₄ := by
    rw [hc₄V]
    exact fun hd => PadicInt.prime_p.not_isUnit
      (isUnit_of_dvd_unit hd ((multTwo_isUnit_neg_three hp2).mul ha₄))
  have hΔV : emultiplicity (p : ℤ_[p]) V.Δ = ((n : ℕ) : ℕ∞) := by
    have h := TateAlgorithm.Step11.run_Δ hϖ hΔ0 hVe
    have h12 : ((12 : ℕ) : ℕ∞) + emultiplicity (p : ℤ_[p]) V.Δ = ((n + 12 : ℕ) : ℕ∞) := by
      rw [← hΔ, ← h, show (p : ℤ_[p]) ^ 12 * V.Δ = (p : ℤ_[p]) ^ 12 * (1 * V.Δ) from by ring,
        PadicInt.emultiplicity_pow_mul_unit_mul 12 isUnit_one]
    obtain ⟨j, hj, hjr⟩ := ENat.exists_natCast_of_add_eq (k := 12) (n := n + 12) h12
    rw [hj, show j = n by omega]
  have hc₆V : -V.c₆ = 27 * b := by
    have h := TateAlgorithm.Step11.run_c₆ hϖ hΔ0 hVe
    rw [ofShortNF_c₆] at h
    have hV6 : V.c₆ = -27 * b := by
      refine mul_left_cancel₀ (pow_ne_zero 6 hϖ) ?_
      rw [h]; subst hp2; push_cast; ring
    rw [hV6]; ring
  obtain ⟨hbu, hbns⟩ := multTwo_isUnit_and_notMem_split_of_nonsplit hp2 hns
  have hpΔV : (p : ℤ_[p]) ∣ V.Δ := dvd_Δ_of_emultiplicity_eq hn hΔV
  have hntan : ¬ TateAlgorithm.Step2.TangentSplits (p : ℤ_[p]) V := by
    rw [TateAlgorithm.Step2.tangentSplits_iff_isSquare_neg_c₆_of_eq_two hp2 hpΔV hc₄, hc₆V]
    exact fun hsq => hbns ((mem_splitSetTwo_iff_isSquare hp2 hbu).2 hsq)
  have hnt : (emultiplicity (p : ℤ_[p]) V.Δ).toNat = n :=
    (toNat_emultiplicity_Δ_eq_iff hVΔ0 n).2 hΔV
  rw [TateAlgorithm.run_eq_of_step11_ok hϖ hΔ0 hVe hVΔ0]
  refine ⟨by rw [run_kodairaSymbol_of_nodal hVΔ0 hpΔV hc₄, hnt], ?_⟩
  rw [run_tamagawaNumber_of_nodal hVΔ0 hpΔV hc₄, ite_eq_right hntan, hnt]

/-! ### The mass of the non-split level set -/

variable (p) in
/-- **The `a₄`-locus carrying the non-split half of the `p = 2` multiplicative shell**:
`a₄ ≡ 13 mod 16`. -/
def multNonSplitFstTwo : Set ℤ_[p] := PadicInt.toZModPow 4 ⁻¹' {(13 : ZMod (p ^ 4))}

/-- The set `multNonSplitFstTwo p` is measurable. -/
theorem measurableSet_multNonSplitFstTwo : MeasurableSet (multNonSplitFstTwo p) :=
  PadicInt.measurableSet_preimage_toZModPow 4 (13 : ZMod (p ^ 4))

/-- The set `multNonSplitFstTwo p` has Haar measure `p⁻⁴`. -/
theorem volume_multNonSplitFstTwo :
    (volume : Measure ℤ_[p]) (multNonSplitFstTwo p) = ((p : ℝ≥0∞) ^ 4)⁻¹ :=
  PadicInt.volume_preimage_toZModPow 4 (13 : ZMod (p ^ 4))

/-- `a₄ ∈ multNonSplitFstTwo p` if and only if `a₄ ≡ 13 mod p⁴`. -/
theorem mem_multNonSplitFstTwo_iff {a₄ : ℤ_[p]} :
    a₄ ∈ multNonSplitFstTwo p ↔ PadicInt.toZModPow 4 a₄ = (13 : ZMod (p ^ 4)) := Iff.rfl

/-- For `p = 2`, every element of `multNonSplitFstTwo p` is a unit. -/
theorem isUnit_of_mem_multNonSplitFstTwo (hp2 : p = 2) {a₄ : ℤ_[p]}
    (h : a₄ ∈ multNonSplitFstTwo p) : IsUnit a₄ := by
  refine not_not.1 fun hnu => ?_
  obtain ⟨k, hk⟩ := PadicInt.dvd_iff_not_isUnit.2 hnu
  have h13 : PadicInt.toZModPow 4 a₄ = (13 : ZMod (p ^ 4)) := h
  rw [hk, map_mul, map_natCast] at h13
  subst hp2
  revert h13
  have hdec : ∀ K : ZMod (2 ^ 4), ((2 : ℕ) : ZMod (2 ^ 4)) * K ≠ 13 := by decide
  exact hdec _

variable (p) in
/-- **The non-split `a₆`-locus** at level `t` over `a₄`: the `a₆ = 2b` with `27b ≡ 5 mod 8` and
`v₂(Δ(a₄, a₆)) = t + 12`. -/
def multNonSplitLevelSet (t : ℕ) (a₄ : ℤ_[p]) : Set ℤ_[p] :=
  {a₆ : ℤ_[p] | (∃ b, a₆ = (p : ℤ_[p]) * b ∧ b ∈ multNonSplitSetTwo p) ∧
    emultiplicity (p : ℤ_[p]) (ofShortNF a₄ a₆).Δ = ((t + 12 : ℕ) : ℕ∞)}

/-- The non-split locus is a rescaled unit-centre level set cut by a congruence modulo `8`. -/
theorem multNonSplitLevelSet_eq_image (hp2 : p = 2) {w : ℤ_[p]} (hw : (27 : ℤ_[p]) * w = 1)
    (t : ℕ) (a₄ : ℤ_[p]) :
    multNonSplitLevelSet p t a₄
      = PadicInt.scaleByPPow 1 ''
          (PadicInt.sqLevelSet (-(a₄ ^ 3) * w) (t + 6) ∩ multNonSplitSetTwo p) := by
  have hval : ∀ b : ℤ_[p],
      emultiplicity (p : ℤ_[p]) (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ = ((t + 12 : ℕ) : ℕ∞) ↔
        b ∈ PadicInt.sqLevelSet (-(a₄ ^ 3) * w) (t + 6) := by
    intro b
    rw [emultiplicity_Δ_two_mul hp2 hw, PadicInt.mem_sqLevelSet]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨j, hj, hjr⟩ := ENat.exists_natCast_of_add_eq (k := 6) (n := t + 12) h
      rw [hj, show j = t + 6 by omega]
    · rw [h]; push_cast; ring
  ext a₆
  simp only [multNonSplitLevelSet, Set.mem_ofPred_eq, Set.mem_image, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨b, rfl, hns⟩, hd⟩
    exact ⟨b, ⟨(hval b).1 hd, hns⟩, by rw [PadicInt.scaleByPPow, pow_one]⟩
  · rintro ⟨b, ⟨hlev, hns⟩, rfl⟩
    rw [PadicInt.scaleByPPow, pow_one]
    exact ⟨⟨b, rfl, hns⟩, (hval b).2 hlev⟩

private theorem multTwo_mem_nonSplit_iff_zmod (hp2 : p = 2) (y : ℤ_[p]) :
    y ∈ multNonSplitSetTwo p ↔ (2 : ZMod (p ^ 4)) * (27 * PadicInt.toZModPow 4 y - 5) = 0 := by
  rw [multNonSplitSetTwo, Set.mem_ofPred_eq,
    PadicInt.pow_three_dvd_iff_two_mul_toZModPow_four_of_eq_two hp2, map_sub, map_mul, map_ofNat,
    map_ofNat]

private theorem multTwo_zmod_nonsplit (hp2 : p = 2) :
    ∀ A S W : ZMod (p ^ 4), 27 * W = 1 → S ^ 2 = -(A ^ 3) * W →
      ((A = 13 → ((2 * (27 * S - 5) = 0 ∧ 2 * (27 * (-S) - 5) ≠ 0) ∨
            (2 * (27 * S - 5) ≠ 0 ∧ 2 * (27 * (-S) - 5) = 0))) ∧
        (A ≠ 13 → (2 * (27 * S - 5) ≠ (0 : ZMod (p ^ 4)) ∧
          2 * (27 * (-S) - 5) ≠ (0 : ZMod (p ^ 4))))) := by
  subst hp2; decide

private theorem multTwo_zmod_isSquare_gamma_nonsplit (hp2 : p = 2) :
    ∀ A W : ZMod (p ^ 4), 27 * W = 1 → A = 13 → 2 * (-(A ^ 3) * W - 1) = (0 : ZMod (p ^ 4)) := by
  subst hp2; decide

/-- **The exact Haar mass of the non-split locus, at every level `t`**: `2^{-(t+7)}` on the class
`a₄ ≡ 13 mod 16` and `0` elsewhere, the same as for the split half. On `a₄ ≡ 13 mod 16` the centre
`γ = -a₄³/27` is `≡ 1 mod 16`, its square roots are `≡ ±1 mod 8`, and `27b ≡ 5 mod 8` keeps exactly
one of the two shells; the other is `b ≡ 1 mod 8`, on which Step 7 answers `Iₘ*`. -/
theorem multTwo_volume_nonSplitLevelSet (hp2 : p = 2) (t : ℕ) {a₄ : ℤ_[p]} (ha₄ : IsUnit a₄) :
    (volume : Measure ℤ_[p]) (multNonSplitLevelSet p t a₄)
      = (multNonSplitFstTwo p).indicator
          (fun _ => (p : ℝ≥0∞)⁻¹ * ((1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ (t + 5))) a₄ := by
  obtain ⟨w, hw⟩ := (multTwo_isUnit_twentySeven hp2).exists_right_inv
  have hwu : IsUnit w := ⟨⟨w, 27, by rw [mul_comm]; exact hw, hw⟩, rfl⟩
  have hγu : IsUnit (-(a₄ ^ 3) * w : ℤ_[p]) := ((ha₄.pow 3).neg).mul hwu
  have hW : (27 : ZMod (p ^ 4)) * PadicInt.toZModPow 4 w = 1 := by
    rw [← map_ofNat (PadicInt.toZModPow 4) 27, ← map_mul, hw, map_one]
  have hQ : ∀ y z : ℤ_[p], (p : ℤ_[p]) ^ 3 ∣ y - z →
      (y ∈ multNonSplitSetTwo p ↔ z ∈ multNonSplitSetTwo p) := fun _ _ h =>
    multTwo_mem_nonSplit_congr h
  rw [multNonSplitLevelSet_eq_image hp2 hw, PadicInt.measure_image_scaleByPPow,
    PadicInt.zpow_neg_natCast_eq_inv_pow_two, pow_one, show t + 6 = t + 5 + 1 by omega]
  by_cases hA : PadicInt.toZModPow 4 a₄ = (13 : ZMod (p ^ 4))
  · rw [Set.indicator_of_mem (mem_multNonSplitFstTwo_iff.2 hA)]
    have hsq : IsSquare (-(a₄ ^ 3) * w : ℤ_[p]) := by
      rw [PadicInt.isSquare_iff_two_mul_toZModPow_four_of_eq_two hp2 hγu, map_mul, map_neg, map_pow]
      exact multTwo_zmod_isSquare_gamma_nonsplit hp2 _ _ hW hA
    obtain ⟨s, hs⟩ := hsq
    have hSrel : (PadicInt.toZModPow 4 s) ^ 2
        = -((PadicInt.toZModPow 4 a₄) ^ 3) * PadicInt.toZModPow 4 w := by
      have h := congrArg (PadicInt.toZModPow (p := p) 4) hs
      rw [map_mul, map_neg, map_pow, map_mul] at h
      rw [h]; ring
    have hone := (multTwo_zmod_nonsplit hp2 (PadicInt.toZModPow 4 a₄) (PadicInt.toZModPow 4 s)
      (PadicInt.toZModPow 4 w) hW hSrel).1 hA
    have hmem_s : s ∈ multNonSplitSetTwo p ↔
        (2 : ZMod (p ^ 4)) * (27 * PadicInt.toZModPow 4 s - 5) = 0 :=
      multTwo_mem_nonSplit_iff_zmod hp2 s
    have hmem_ns : -s ∈ multNonSplitSetTwo p ↔
        (2 : ZMod (p ^ 4)) * (27 * (-(PadicInt.toZModPow 4 s)) - 5) = 0 := by
      rw [multTwo_mem_nonSplit_iff_zmod hp2, map_neg]
    rw [PadicInt.volume_sqLevelSet_inter_of_unique_root_of_eq_two hp2 hγu hs hQ ?_
      (by omega : 3 ≤ t + 5)]
    rcases hone with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hmem_s.2 h1, fun hc => h2 (hmem_ns.1 hc)⟩
    · exact Or.inr ⟨fun hc => h1 (hmem_s.1 hc), hmem_ns.2 h2⟩
  · rw [Set.indicator_of_notMem (fun hc => hA (mem_multNonSplitFstTwo_iff.1 hc))]
    by_cases hsq : IsSquare (-(a₄ ^ 3) * w : ℤ_[p])
    · obtain ⟨s, hs⟩ := hsq
      have hSrel : (PadicInt.toZModPow 4 s) ^ 2
          = -((PadicInt.toZModPow 4 a₄) ^ 3) * PadicInt.toZModPow 4 w := by
        have h := congrArg (PadicInt.toZModPow (p := p) 4) hs
        rw [map_mul, map_neg, map_pow, map_mul] at h
        rw [h]; ring
      have hnone := (multTwo_zmod_nonsplit hp2 (PadicInt.toZModPow 4 a₄) (PadicInt.toZModPow 4 s)
        (PadicInt.toZModPow 4 w) hW hSrel).2 hA
      rw [PadicInt.volume_sqLevelSet_inter_of_no_root_of_eq_two hp2 hγu hs hQ
        ⟨fun hc => hnone.1 ((multTwo_mem_nonSplit_iff_zmod hp2 s).1 hc),
          fun hc => hnone.2 (by
            have h := (multTwo_mem_nonSplit_iff_zmod hp2 (-s)).1 hc
            rwa [map_neg] at h)⟩ (by omega : 3 ≤ t + 5), mul_zero]
    · rw [PadicInt.sqLevelSet_eq_empty_of_not_isSquare_of_eq_two hp2 hγu hsq
        (by omega : 3 ≤ t + 5 + 1), Set.empty_inter, measure_empty, mul_zero]

/-! ### The non-split loci and their mass -/

variable (p) in
/-- **The non-split multiplicative locus at level `n`**: `a₄ ≡ 13 mod 16`, `a₆ ≡ 14 mod 16` and
`v₂(Δ) = n + 12`. -/
noncomputable def multNonSplitLocusTwo (n : ℕ) : Set (ℤ_[p] × ℤ_[p]) :=
  (Prod.fst ⁻¹' (PadicInt.toZModPow 4 ⁻¹' {(13 : ZMod (p ^ 4))})) ∩
    (Prod.snd ⁻¹' (PadicInt.toZModPow 4 ⁻¹' {(14 : ZMod (p ^ 4))})) ∩
    ((fun x : ℤ_[p] × ℤ_[p] => (ofShortNF x.1 x.2).Δ) ⁻¹'
      {y : ℤ_[p] | emultiplicity (p : ℤ_[p]) y = ((n + 12 : ℕ) : ℕ∞)})

/-- Membership in `multNonSplitLocusTwo p n` unfolds to its three defining conditions. -/
theorem mem_multNonSplitLocusTwo_iff {n : ℕ} {x : ℤ_[p] × ℤ_[p]} :
    x ∈ multNonSplitLocusTwo p n ↔ PadicInt.toZModPow 4 x.1 = (13 : ZMod (p ^ 4)) ∧
      PadicInt.toZModPow 4 x.2 = (14 : ZMod (p ^ 4)) ∧
      emultiplicity (p : ℤ_[p]) (ofShortNF x.1 x.2).Δ = ((n + 12 : ℕ) : ℕ∞) :=
  ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- The non-split multiplicative locus `multNonSplitLocusTwo p n` is measurable. -/
theorem measurableSet_multNonSplitLocusTwo (n : ℕ) :
    MeasurableSet (multNonSplitLocusTwo p n) :=
  (((PadicInt.measurableSet_preimage_toZModPow 4 _).preimage measurable_fst).inter
      ((PadicInt.measurableSet_preimage_toZModPow 4 _).preimage measurable_snd)).inter
    ((PadicInt.measurableSet_setOf_emultiplicity_eq (n + 12)).preimage
      continuous_shortNF_Δ.measurable)

/-- For `p = 2`, the `a₆`-slice of the non-split locus over an `a₄ ≡ 13 mod 16` is the non-split
level set `multNonSplitLevelSet p n a₄`. -/
theorem multTwo_nonsplit_slice_eq (hp2 : p = 2) (n : ℕ) {a₄ : ℤ_[p]}
    (ha₄ : PadicInt.toZModPow 4 a₄ = (13 : ZMod (p ^ 4))) :
    Prod.mk a₄ ⁻¹' multNonSplitLocusTwo p n = multNonSplitLevelSet p n a₄ := by
  ext a₆
  rw [Set.mem_preimage, mem_multNonSplitLocusTwo_iff, multNonSplitLevelSet, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨(multTwo_toZModPow_four_eq_fourteen_iff hp2).1 h.2.1, h.2.2⟩,
    fun h => ⟨ha₄, (multTwo_toZModPow_four_eq_fourteen_iff hp2).2 h.1, h.2⟩⟩

/-- The `a₆`-slice of the non-split locus over an `a₄ ≢ 13 mod p⁴` is empty. -/
theorem multTwo_nonsplit_slice_eq_empty (n : ℕ) {a₄ : ℤ_[p]}
    (ha₄ : PadicInt.toZModPow 4 a₄ ≠ (13 : ZMod (p ^ 4))) :
    Prod.mk a₄ ⁻¹' multNonSplitLocusTwo p n = (∅ : Set ℤ_[p]) :=
  Set.eq_empty_iff_forall_notMem.2 fun _ hx => ha₄ (mem_multNonSplitLocusTwo_iff.1 hx).1

/-- **The mass of the non-split multiplicative locus is `2^{-(n+11)}`**, equal to the split one. -/
theorem volume_multNonSplitLocusTwo (hp2 : p = 2) (n : ℕ) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (multNonSplitLocusTwo p n)
      = (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ (n + 10) := by
  have hslice : ∀ a₄ : ℤ_[p],
      (volume : Measure ℤ_[p]) (Prod.mk a₄ ⁻¹' multNonSplitLocusTwo p n)
        = (multNonSplitFstTwo p).indicator
            (fun _ => (p : ℝ≥0∞)⁻¹ * ((1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞)⁻¹) ^ (n + 5))) a₄ := by
    intro a₄
    by_cases ha₄ : PadicInt.toZModPow 4 a₄ = (13 : ZMod (p ^ 4))
    · rw [multTwo_nonsplit_slice_eq hp2 n ha₄,
        multTwo_volume_nonSplitLevelSet hp2 n (isUnit_of_mem_multNonSplitFstTwo hp2
          (mem_multNonSplitFstTwo_iff.2 ha₄))]
    · rw [multTwo_nonsplit_slice_eq_empty n ha₄, measure_empty,
        Set.indicator_of_notMem (fun hc => ha₄ (mem_multNonSplitFstTwo_iff.1 hc))]
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_multNonSplitLocusTwo n),
    lintegral_congr hslice, lintegral_indicator_const measurableSet_multNonSplitFstTwo,
    volume_multNonSplitFstTwo, ENNReal.inv_pow, show n + 10 = 4 + (1 + (n + 5)) by omega,
    pow_add, pow_add]
  ring

/-! ### Tate's algorithm on the non-split loci -/

/-- A point of the non-split multiplicative locus has nonzero discriminant. -/
theorem multTwo_nonsplit_Δ_ne_zero_of_mem {n : ℕ} {x : ℤ_[p] × ℤ_[p]}
    (hx : x ∈ multNonSplitLocusTwo p n) : (ofShortNF x.1 x.2).Δ ≠ 0 := by
  intro h0
  have hd := (mem_multNonSplitLocusTwo_iff.1 hx).2.2
  rw [h0, emultiplicity_zero_right] at hd
  exact (ENat.natCast_ne_top (n + 12)) hd.symm

open scoped Classical in
/-- **On the non-split locus at level `n ≥ 1` Tate's algorithm answers `(Iₙ, 1)` for odd `n` and
`(Iₙ, 2)` for even `n`.** -/
theorem multTwo_run_eq_I_of_mem_nonsplit (hp2 : p = 2) {n : ℕ} (hn : 1 ≤ n) {a₄ a₆ : ℤ_[p]}
    (hx : ((a₄, a₆) : ℤ_[p] × ℤ_[p]) ∈ multNonSplitLocusTwo p n)
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.I n ∧
      (TateAlgorithm.run (W := ofShortNF a₄ a₆)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = (if Odd n then 1 else 2) := by
  have hπ : (p : ℤ_[p]) = 2 := by subst hp2; norm_num
  obtain ⟨ha, hfourteen, hd⟩ := mem_multNonSplitLocusTwo_iff.1 hx
  obtain ⟨b, hb, hns⟩ := (multTwo_toZModPow_four_eq_fourteen_iff hp2).1 hfourteen
  subst hb
  have ha₄u : IsUnit a₄ :=
    isUnit_of_mem_multNonSplitFstTwo hp2 (mem_multNonSplitFstTwo_iff.2 ha)
  have h12 : (p : ℤ_[p]) ^ 12 ∣ (ofShortNF a₄ ((p : ℤ_[p]) * b)).Δ :=
    pow_dvd_of_le_emultiplicity (by rw [hd]; exact_mod_cast (by omega : 12 ≤ n + 12))
  obtain ⟨α, k, hα, hk⟩ :=
    multTwo_exists_params_nonsplit_of_dvd_twelve hp2 (by rw [hπ]) hns h12
  exact multTwo_run_eq_I_of_nonsplit hp2 hn ha₄u hns hd hΔ0
    (TateAlgorithm.Step11.run_eq_ok_of_params_nonsplit_two hp2 hΔ0 (b := b) (α := α) (k := k)
      (by rw [hπ]) ha₄u hα hk)

open scoped Classical in
/-- **On the non-split locus at level `n ≥ 1` Tate's algorithm answers `(Iₙ, 1)` for odd `n` and
`(Iₙ, 2)` for even `n`**, stated for a point of the plane. -/
theorem multTwo_run_eq_I_of_mem_nonsplit' (hp2 : p = 2) {n : ℕ} (hn : 1 ≤ n)
    {x : ℤ_[p] × ℤ_[p]} (hx : x ∈ multNonSplitLocusTwo p n)
    (hΔ0 : (ofShortNF x.1 x.2).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ0).kodairaSymbol = KodairaSymbol.I n ∧
      (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ0).tamagawaNumber = (if Odd n then 1 else 2) :=
  multTwo_run_eq_I_of_mem_nonsplit hp2 hn hx hΔ0

/-- **The non-split locus at an odd level lies in the minimal part of the `t = 1` row.** -/
theorem multNonSplitLocusTwo_subset_headMinimal_odd (hp2 : p = 2) {n : ℕ} (hn : 1 ≤ n)
    (hodd : Odd n) :
    multNonSplitLocusTwo p n ⊆ (⋃ κ : KodairaSymbol, stratFibre p (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := multTwo_nonsplit_Δ_ne_zero_of_mem hx
  have hUp : x ∈ nonsingularLocus p := hΔ
  obtain ⟨hκ, ht⟩ := multTwo_run_eq_I_of_mem_nonsplit' hp2 hn hx hΔ
  rw [ite_eq_left hodd] at ht
  refine ⟨Set.mem_iUnion.2 ⟨KodairaSymbol.I n,
    (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ ht)⟩, ?_⟩
  exact notMem_range_of_isUnit_fst_two (isUnit_of_mem_multNonSplitFstTwo hp2
    (mem_multNonSplitFstTwo_iff.2 (mem_multNonSplitLocusTwo_iff.1 hx).1))

/-- **The non-split locus at an even level lies in the minimal part of the `t = 2` row.** -/
theorem multNonSplitLocusTwo_subset_headMinimal_even (hp2 : p = 2) {n : ℕ} (hn : 1 ≤ n)
    (heven : ¬ Odd n) :
    multNonSplitLocusTwo p n ⊆ (⋃ κ : KodairaSymbol, stratFibre p (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[p] × ℤ_[p] → ℤ_[p] × ℤ_[p]) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := multTwo_nonsplit_Δ_ne_zero_of_mem hx
  have hUp : x ∈ nonsingularLocus p := hΔ
  obtain ⟨hκ, ht⟩ := multTwo_run_eq_I_of_mem_nonsplit' hp2 hn hx hΔ
  rw [ite_eq_right heven] at ht
  refine ⟨Set.mem_iUnion.2 ⟨KodairaSymbol.I n,
    (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ ht)⟩, ?_⟩
  exact notMem_range_of_isUnit_fst_two (isUnit_of_mem_multNonSplitFstTwo hp2
    (mem_multNonSplitFstTwo_iff.2 (mem_multNonSplitLocusTwo_iff.1 hx).1))

/-- **Loci at distinct levels are disjoint**, the level being `v₂(Δ) - 12`. -/
theorem multTwo_disjoint_nonsplit {n n' : ℕ} (h : n ≠ n') :
    Disjoint (multNonSplitLocusTwo p n) (multNonSplitLocusTwo p n') := by
  refine Set.disjoint_left.2 fun x hx hx' => h ?_
  have h1 := (mem_multNonSplitLocusTwo_iff.1 hx).2.2
  have h2 := (mem_multNonSplitLocusTwo_iff.1 hx').2.2
  have heq : ((n + 12 : ℕ) : ℕ∞) = ((n' + 12 : ℕ) : ℕ∞) := h1.symm.trans h2
  have : n + 12 = n' + 12 := by exact_mod_cast heq
  omega

/-! ### The mass of the non-split locus at `p = 2`, evaluated -/

/-- **The mass of the non-split locus, evaluated:** `2^{-(n+11)}`. -/
theorem volume_multNonSplitLocusTwo_at_two (n : ℕ) :
    (volume : Measure (ℤ_[2] × ℤ_[2])) (multNonSplitLocusTwo 2 n)
      = ((2 : ℝ≥0∞)⁻¹) ^ (n + 11) := by
  have h2 : ((2 : ℕ) : ℝ≥0∞) = 2 := by norm_num
  have hpow : ((2 : ℝ≥0∞)⁻¹) ^ (n + 11) = (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ (n + 10) := by
    rw [show n + 11 = (n + 10) + 1 from by omega, pow_succ]; ring
  rw [volume_multNonSplitLocusTwo (p := 2) rfl n, multTwo_one_sub_inv (p := 2) rfl, h2, hpow]

end WeierstrassCurve

end
