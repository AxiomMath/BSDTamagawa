/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.ReductionValuation
public import BSDTamagawa.Equidistribution.ResidueClass

/-!
# Per-prime uniform-`X` exceptional reduction-type tail bound

For the family of nonsingular integral short Weierstrass curves `E(a₄,a₆) : y² = x³ + a₄x + a₆`,
the proportion, among curves of height `≤ X`, of those whose local reduction datum `τ_p(E)` at a
prime `p ≥ 5` is not one of the trivial types in `𝒦₀` (good reduction, or multiplicative type `I₁`)
satisfies `N_p^{∉𝒦₀}(X) / N(X) ≤ C (1/p² + 1/(p X^{1/3}) + 1/X^{1/2})`, with `C` uniform in `p` and
`X`. Since `τ_p(E) ∉ 𝒦₀` implies `p² ∣ Δ`, this reduces to counting the lattice points of the
height box satisfying the congruence `p² ∣ 4a₄³ + 27a₆²`.

## Main definitions

* `exceptionalCount`: the number of nonsingular curves of height `≤ X` whose reduction datum at
  `p` lies outside `𝒦₀`.
* `discBoxCount`: the number of nonsingular `(a₄, a₆)` of height `≤ X` with `p² ∣ 4a₄³ + 27a₆²`.

## Main results

* `exceptional_le_discBoxCount`: for `p ≥ 5`, `exceptionalCount p X ≤ discBoxCount p X`.
* `discBoxCount_le`: `discBoxCount p X ≤ C₁ N(X) (1/p² + 1/(p X^{1/3}) + 1/X^{1/2})` uniformly in
  `p ≥ 5` and `X ≥ 4`.
* `exceptional_ratio_bound`: the uniform bound on the exceptional proportion.
-/

@[expose] public section

open WeierstrassCurve

namespace ShortWeierstrassReductionStatistics

/-! ### Elementary divisibility facts -/

/-- A prime `p` does not divide `c = q ^ n` when `0 < q < p`. -/
theorem not_dvd_of_eq_pow {p : ℕ} (hp : p.Prime) (q n : ℕ) (hq : 0 < q) (hqp : q < p)
    {c : ℤ} (hc : c = (q : ℤ) ^ n) : ¬ (p : ℤ) ∣ c := by
  rw [hc]
  intro hdvd
  have hpn : p ∣ q ^ n := by exact_mod_cast hdvd
  exact absurd (Nat.le_of_dvd hq (hp.dvd_of_dvd_pow hpn)) (by omega)

/-- If a prime `p` does not divide `a`, then `p ^ 2` and `a` are coprime in `ℤ`. -/
theorem isCoprime_sq_of_not_dvd {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    IsCoprime ((p : ℤ) ^ 2) a :=
  (((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr ha).pow_left

/-! ## The exceptional count and its arithmetic proxy -/

/-- The number of nonsingular height-`≤ X` curves whose local reduction datum `τ_p` at `p` is not
one of the trivial types in `𝒦₀ = {(I₀,1), (I₁,1)}`. -/
noncomputable def exceptionalCount (p : ℕ) [Fact p.Prime] (X : ℝ) : ℕ :=
  {q : ℤ × ℤ | (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
      ((tauZ p q.1 q.2).kodairaSymbol, (tauZ p q.1 q.2).tamagawaNumber) ∉ K0}.ncard

/-- The number of lattice points `(a₄, a₆)` of height `≤ X` that are non-singular
(`4a₄³+27a₆² ≠ 0`) and satisfy the congruence `p² ∣ (4a₄³+27a₆²)`. -/
noncomputable def discBoxCount (p : ℕ) (X : ℝ) : ℕ :=
  {q : ℤ × ℤ |
      (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ 4 * q.1 ^ 3 + 27 * q.2 ^ 2 ≠ 0 ∧
        (p : ℤ) ^ 2 ∣ (4 * q.1 ^ 3 + 27 * q.2 ^ 2)}.ncard

/-- For `X ≥ 0`, `discBoxCount p X` is at most the number of points of the height box `heightBox X`
that are non-singular and satisfy `p² ∣ 4a₄³ + 27a₆²`. -/
theorem discBoxCount_le_finset (p : ℕ) (X : ℝ) (hX : 0 ≤ X) :
    discBoxCount p X ≤
      ((heightBox X).filter (fun q => 4 * q.1 ^ 3 + 27 * q.2 ^ 2 ≠ 0 ∧
        (p : ℤ) ^ 2 ∣ (4 * q.1 ^ 3 + 27 * q.2 ^ 2))).card := by
  unfold discBoxCount
  refine le_trans (Set.ncard_le_ncard ?_ (Finset.finite_toSet _)) (Set.ncard_coe_finset _).le
  rintro q ⟨hh, hne, hdvd⟩
  exact Finset.mem_coe.mpr
    (Finset.mem_filter.mpr ⟨(mem_heightBox_iff hX q).mpr hh, hne, hdvd⟩)

/-- For `p ≥ 5` prime with `p ∤ a4`, any two solutions `x, y` of `p² ∣ 4a4³ + 27·(·)²` satisfy
`p² ∣ x - y` or `p² ∣ x + y`. -/
theorem sq_equiv_of_p2_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (a4 x y : ℤ)
    (hpa4 : ¬ (p : ℤ) ∣ a4)
    (hx : (p : ℤ) ^ 2 ∣ 4 * a4 ^ 3 + 27 * x ^ 2)
    (hy : (p : ℤ) ^ 2 ∣ 4 * a4 ^ 3 + 27 * y ^ 2) :
    (p : ℤ) ^ 2 ∣ x - y ∨ (p : ℤ) ^ 2 ∣ x + y := by
  have hpprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsub : (p : ℤ) ^ 2 ∣ 27 * ((x - y) * (x + y)) := by
    have hd := dvd_sub hx hy
    rwa [show (4 * a4 ^ 3 + 27 * x ^ 2) - (4 * a4 ^ 3 + 27 * y ^ 2)
      = 27 * ((x - y) * (x + y)) by ring] at hd
  have hp27 : ¬ (p : ℤ) ∣ (27 : ℤ) :=
    not_dvd_of_eq_pow hp 3 3 (by norm_num) (by omega) (by norm_num)
  have hprod : (p : ℤ) ^ 2 ∣ (x - y) * (x + y) :=
    (isCoprime_sq_of_not_dvd hp hp27).dvd_of_dvd_mul_left hsub
  by_cases hpx : (p : ℤ) ∣ (x - y)
  · by_cases hpy : (p : ℤ) ∣ (x + y)
    · exfalso
      have h2x : (p : ℤ) ∣ 2 * x := by
        have hd := dvd_add hpx hpy
        rwa [show (x - y) + (x + y) = 2 * x by ring] at hd
      have hp2 : ¬ (p : ℤ) ∣ (2 : ℤ) :=
        not_dvd_of_eq_pow hp 2 1 (by norm_num) (by omega) (by norm_num)
      have hp4 : ¬ (p : ℤ) ∣ (4 : ℤ) :=
        not_dvd_of_eq_pow hp 2 2 (by norm_num) (by omega) (by norm_num)
      have hpx' : (p : ℤ) ∣ x := (hpprime.dvd_mul.mp h2x).resolve_left hp2
      have hp24a4 : (p : ℤ) ^ 2 ∣ 4 * a4 ^ 3 := by
        have hd := dvd_sub hx ((pow_dvd_pow_of_dvd hpx' 2).mul_left 27)
        rwa [show (4 * a4 ^ 3 + 27 * x ^ 2) - 27 * x ^ 2 = 4 * a4 ^ 3 by ring] at hd
      have hp2a43 : (p : ℤ) ^ 2 ∣ a4 ^ 3 :=
        (isCoprime_sq_of_not_dvd hp hp4).dvd_of_dvd_mul_left hp24a4
      exact hpa4 (hpprime.dvd_of_dvd_pow ((dvd_pow_self _ (by norm_num)).trans hp2a43))
    · exact Or.inl ((isCoprime_sq_of_not_dvd hp hpy).dvd_of_dvd_mul_right hprod)
  · exact Or.inr ((isCoprime_sq_of_not_dvd hp hpx).dvd_of_dvd_mul_left hprod)

/-- For `m > 0`, the number of integers `z ∈ [-L, L]` with `m ∣ z - r` is at most `2L/m + 1`. -/
theorem card_Icc_filter_dvd_sub_le (m : ℕ) (hm : 0 < m) (L : ℕ) (r : ℤ) :
    (((Finset.Icc (-(L : ℤ)) (L : ℤ)).filter (fun z => (m : ℤ) ∣ z - r)).card : ℝ)
      ≤ 2 * (L : ℝ) / (m : ℝ) + 1 := by
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set S := (Finset.Icc (-(L : ℤ)) (L : ℤ)).filter (fun z => (m : ℤ) ∣ z - r) with hSdef
  set hi : ℤ := ((L : ℤ) - r) / (m : ℤ) with hhi
  set lo : ℤ := -(((L : ℤ) + r) / (m : ℤ)) with hlo
  have hmapmem : ∀ z ∈ S, (z - r) / (m : ℤ) ∈ Finset.Icc lo hi := by
    intro z hz
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hz
    obtain ⟨⟨hzlo, hzhi⟩, hdvd⟩ := hz
    have hk : (m : ℤ) * ((z - r) / (m : ℤ)) = z - r := Int.mul_ediv_cancel' hdvd
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · rw [hlo, neg_le, Int.le_ediv_iff_mul_le hmZ]; linarith
    · rw [hhi, Int.le_ediv_iff_mul_le hmZ]; linarith
  have hinj : Set.InjOn (fun z => (z - r) / (m : ℤ)) ↑S := by
    intro x hx y hy hxy
    rw [hSdef, Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
    have hex := Int.mul_ediv_cancel' hx.2
    have hey := Int.mul_ediv_cancel' hy.2
    simp only at hxy
    have : x - r = y - r := by rw [← hex, ← hey, hxy]
    omega
  have hcard_le : S.card ≤ (Finset.Icc lo hi).card :=
    Finset.card_le_card_of_injOn (fun z => (z - r) / (m : ℤ)) hmapmem hinj
  have hhiR : (hi : ℝ) ≤ ((L : ℝ) - r) / (m : ℝ) := by
    have hZ : hi * (m : ℤ) ≤ (L : ℤ) - r := by
      rw [hhi]; exact Int.ediv_mul_le _ (by omega)
    rw [le_div_iff₀ hmR]; exact_mod_cast hZ
  have hnegloR : -(lo : ℝ) ≤ ((L : ℝ) + r) / (m : ℝ) := by
    have hZ : -lo * (m : ℤ) ≤ (L : ℤ) + r := by
      rw [hlo, neg_neg]; exact Int.ediv_mul_le _ (by omega)
    rw [le_div_iff₀ hmR]; exact_mod_cast hZ
  have hsum : (hi : ℝ) - (lo : ℝ) ≤ 2 * (L : ℝ) / (m : ℝ) := by
    have hcomb : ((L : ℝ) - r) / (m : ℝ) + ((L : ℝ) + r) / (m : ℝ) =
        2 * (L : ℝ) / (m : ℝ) := by
      field_simp; ring
    linarith
  rcases S.eq_empty_or_nonempty with hSe | ⟨z0, hz0mem⟩
  · rw [hSe, Finset.card_empty, Nat.cast_zero]; positivity
  · have hle : lo ≤ hi := by
      have := Finset.mem_Icc.mp (hmapmem z0 hz0mem); omega
    have hcardZ : (S.card : ℤ) ≤ hi - lo + 1 := by
      calc (S.card : ℤ) ≤ ((Finset.Icc lo hi).card : ℤ) := by exact_mod_cast hcard_le
        _ = hi - lo + 1 := by rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]; ring
    have hcardR : (S.card : ℝ) ≤ (hi : ℝ) - (lo : ℝ) + 1 := by exact_mod_cast hcardZ
    linarith

/-- For `p > 0`, the number of integers `z ∈ [-L, L]` divisible by `p` is at most `2L/p + 1`. -/
theorem card_Icc_filter_dvd_le (p L : ℕ) (hp : 0 < p) :
    (((Finset.Icc (-(L : ℤ)) (L : ℤ)).filter (fun z => (p : ℤ) ∣ z)).card : ℝ)
      ≤ 2 * (L : ℝ) / (p : ℝ) + 1 := by
  simpa using card_Icc_filter_dvd_sub_le p hp L 0

/-- For fixed `a4` with `p ∤ a4` (p ≥ 5 prime): the number of `a6 ∈ [-a₆Bound, a₆Bound]` with
`p² ∣ (4a4³ + 27a6²)` is `≤ 2·((2a₆Bound+1)/p² + 1)`. -/
theorem per_a4_count_A1 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (a4 : ℤ)
    (hpa4 : ¬ (p : ℤ) ∣ a4) (a₆Bound : ℕ) :
    (((Finset.Icc (-(a₆Bound : ℤ)) (a₆Bound : ℤ)).filter
        (fun a6 => (p : ℤ) ^ 2 ∣ (4 * a4 ^ 3 + 27 * a6 ^ 2))).card : ℝ) ≤
      2 * ((2 * (a₆Bound : ℝ) + 1) / (p : ℝ) ^ 2 + 1) := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hm : 0 < p ^ 2 := by positivity
  set S := (Finset.Icc (-(a₆Bound : ℤ)) (a₆Bound : ℤ)).filter
      (fun a6 => (p : ℤ) ^ 2 ∣ (4 * a4 ^ 3 + 27 * a6 ^ 2)) with hSdef
  rcases S.eq_empty_or_nonempty with hSe | ⟨r, hrS⟩
  · rw [hSe, Finset.card_empty, Nat.cast_zero]; positivity
  · rw [hSdef, Finset.mem_filter] at hrS
    obtain ⟨-, hrdvd⟩ := hrS
    set T1 := (Finset.Icc (-(a₆Bound : ℤ)) (a₆Bound : ℤ)).filter
      (fun z => (p : ℤ) ^ 2 ∣ z - r) with hT1
    set T2 := (Finset.Icc (-(a₆Bound : ℤ)) (a₆Bound : ℤ)).filter
      (fun z => (p : ℤ) ^ 2 ∣ z - (-r)) with hT2
    have hsub : S ⊆ T1 ∪ T2 := by
      intro a6 ha6
      rw [hSdef, Finset.mem_filter] at ha6
      obtain ⟨hmem, hdvd⟩ := ha6
      have hor := sq_equiv_of_p2_dvd p hp hp5 a4 a6 r hpa4 hdvd hrdvd
      rw [Finset.mem_union, hT1, hT2, Finset.mem_filter, Finset.mem_filter]
      rcases hor with h | h
      · exact Or.inl ⟨hmem, h⟩
      · refine Or.inr ⟨hmem, ?_⟩
        simpa [sub_neg_eq_add] using h
    have hcard_le : (S.card : ℝ) ≤ (T1.card : ℝ) + (T2.card : ℝ) := by
      have hh : S.card ≤ T1.card + T2.card :=
        (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      exact_mod_cast hh
    have hpsq : ((p ^ 2 : ℕ) : ℝ) = (p : ℝ) ^ 2 := by push_cast; ring
    have hT1le : (T1.card : ℝ) ≤ 2 * (a₆Bound : ℝ) / (p : ℝ) ^ 2 + 1 := by
      rw [hT1]; simpa [hpsq] using card_Icc_filter_dvd_sub_le (p ^ 2) hm a₆Bound r
    have hT2le : (T2.card : ℝ) ≤ 2 * (a₆Bound : ℝ) / (p : ℝ) ^ 2 + 1 := by
      rw [hT2]; simpa [hpsq] using card_Icc_filter_dvd_sub_le (p ^ 2) hm a₆Bound (-r)
    have hp2pos : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    have hmono : 2 * (a₆Bound : ℝ) / (p : ℝ) ^ 2 ≤ (2 * (a₆Bound : ℝ) + 1) / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) hp2pos.le
    linarith

/-- For fixed `a4` with `p ∣ a4` (p ≥ 5 prime): the number of `a6 ∈ [-a₆Bound, a₆Bound]` with
`p² ∣ (4a4³ + 27a6²)` is `≤ 2a₆Bound/p + 1`. -/
theorem per_a4_count_A0 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (a4 : ℤ)
    (hpa4 : (p : ℤ) ∣ a4) (a₆Bound : ℕ) :
    (((Finset.Icc (-(a₆Bound : ℤ)) (a₆Bound : ℤ)).filter
        (fun a6 => (p : ℤ) ^ 2 ∣ (4 * a4 ^ 3 + 27 * a6 ^ 2))).card : ℝ) ≤
      2 * (a₆Bound : ℝ) / (p : ℝ) + 1 := by
  have hpprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨t, ht⟩ := hpa4
  have hp2dvd4 : (p : ℤ) ^ 2 ∣ 4 * a4 ^ 3 := ⟨4 * (p : ℤ) * t ^ 3, by rw [ht]; ring⟩
  have hsub : (Finset.Icc (-(a₆Bound : ℤ)) (a₆Bound : ℤ)).filter
        (fun a6 => (p : ℤ) ^ 2 ∣ (4 * a4 ^ 3 + 27 * a6 ^ 2)) ⊆
      (Finset.Icc (-(a₆Bound : ℤ)) (a₆Bound : ℤ)).filter (fun a6 => (p : ℤ) ∣ a6) := by
    intro a6 ha6
    rw [Finset.mem_filter] at ha6 ⊢
    refine ⟨ha6.1, ?_⟩
    have hcop : IsCoprime ((p : ℤ) ^ 2) (27 : ℤ) :=
      isCoprime_sq_of_not_dvd hp (not_dvd_of_eq_pow hp 3 3 (by norm_num) (by omega) (by norm_num))
    have h27 : (p : ℤ) ^ 2 ∣ 27 * a6 ^ 2 := by
      have hd := dvd_sub ha6.2 hp2dvd4
      rwa [show (4 * a4 ^ 3 + 27 * a6 ^ 2) - 4 * a4 ^ 3 = 27 * a6 ^ 2 by ring] at hd
    exact hpprime.dvd_of_dvd_pow
      ((dvd_pow_self _ (by norm_num)).trans (hcop.dvd_of_dvd_mul_left h27))
  exact le_trans (by exact_mod_cast Finset.card_le_card hsub)
    (card_Icc_filter_dvd_le p a₆Bound hp.pos)

/-- For `p ≥ 5` prime, the number of non-singular
`(a₄, a₆) ∈ [-a₄Bound, a₄Bound] × [-a₆Bound, a₆Bound]` with `p² ∣ 4a₄³ + 27a₆²` is at most
`2(2a₄Bound+1)((2a₆Bound+1)/p² + 1) + (2a₄Bound/p + 1)(2a₆Bound/p + 1)`. -/
theorem filteredBox_card_le (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (a₄Bound a₆Bound : ℕ) :
    (((Finset.Icc (-(a₄Bound : ℤ)) (a₄Bound : ℤ) ×ˢ
        Finset.Icc (-(a₆Bound : ℤ)) (a₆Bound : ℤ)).filter
        (fun q => 4 * q.1 ^ 3 + 27 * q.2 ^ 2 ≠ 0 ∧
          (p : ℤ) ^ 2 ∣ (4 * q.1 ^ 3 + 27 * q.2 ^ 2))).card : ℝ) ≤
      2 * (2 * (a₄Bound : ℝ) + 1) * ((2 * (a₆Bound : ℝ) + 1) / (p : ℝ) ^ 2 + 1) +
        (2 * (a₄Bound : ℝ) / (p : ℝ) + 1) * (2 * (a₆Bound : ℝ) / (p : ℝ) + 1) := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  set A : Finset ℤ := Finset.Icc (-(a₄Bound : ℤ)) (a₄Bound : ℤ) with hA
  set B : Finset ℤ := Finset.Icc (-(a₆Bound : ℤ)) (a₆Bound : ℤ) with hB
  set g : ℤ → ℕ := fun a4 =>
    (B.filter (fun a6 => (p : ℤ) ^ 2 ∣ (4 * a4 ^ 3 + 27 * a6 ^ 2))).card with hg
  have hstep1 :
      ((A ×ˢ B).filter (fun q => 4 * q.1 ^ 3 + 27 * q.2 ^ 2 ≠ 0 ∧
          (p : ℤ) ^ 2 ∣ (4 * q.1 ^ 3 + 27 * q.2 ^ 2))).card ≤ ∑ a4 ∈ A, g a4 := by
    have hsub : (A ×ˢ B).filter (fun q => 4 * q.1 ^ 3 + 27 * q.2 ^ 2 ≠ 0 ∧
          (p : ℤ) ^ 2 ∣ (4 * q.1 ^ 3 + 27 * q.2 ^ 2)) ⊆
        (A ×ˢ B).filter (fun q => (p : ℤ) ^ 2 ∣ (4 * q.1 ^ 3 + 27 * q.2 ^ 2)) := by
      intro q hq
      rw [Finset.mem_filter] at hq ⊢
      exact ⟨hq.1, hq.2.2⟩
    refine le_trans (Finset.card_le_card hsub) (le_of_eq ?_)
    rw [Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a4 _
    rw [hg]
    simp only [Finset.card_filter]
  have hAdvd_bound : ∀ a4 ∈ A.filter (fun a4 => (p : ℤ) ∣ a4),
      (g a4 : ℝ) ≤ 2 * (a₆Bound : ℝ) / (p : ℝ) + 1 := fun a4 ha4 =>
    per_a4_count_A0 p hp hp5 a4 (Finset.mem_filter.mp ha4).2 a₆Bound
  have hAndvd_bound : ∀ a4 ∈ A.filter (fun a4 => ¬ (p : ℤ) ∣ a4),
      (g a4 : ℝ) ≤ 2 * ((2 * (a₆Bound : ℝ) + 1) / (p : ℝ) ^ 2 + 1) := fun a4 ha4 =>
    per_a4_count_A1 p hp hp5 a4 (Finset.mem_filter.mp ha4).2 a₆Bound
  have hsplit : (∑ a4 ∈ A, g a4 : ℝ) =
      (∑ a4 ∈ A.filter (fun a4 => (p : ℤ) ∣ a4), (g a4 : ℝ)) +
      (∑ a4 ∈ A.filter (fun a4 => ¬ (p : ℤ) ∣ a4), (g a4 : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not A (fun a4 => (p : ℤ) ∣ a4)
      (fun a4 => (g a4 : ℝ))).symm
  have hdvdcard :
      ((A.filter (fun a4 => (p : ℤ) ∣ a4)).card : ℝ) ≤ 2 * (a₄Bound : ℝ) / (p : ℝ) + 1 :=
    card_Icc_filter_dvd_le p a₄Bound hp.pos
  have hndvdcard :
      ((A.filter (fun a4 => ¬ (p : ℤ) ∣ a4)).card : ℝ) ≤ 2 * (a₄Bound : ℝ) + 1 := by
    have hAcard : A.card = 2 * a₄Bound + 1 := by rw [hA, Int.card_Icc]; omega
    have h := (Finset.card_filter_le A (fun a4 => ¬ (p : ℤ) ∣ a4)).trans hAcard.le
    exact_mod_cast h
  have hdvdsum : (∑ a4 ∈ A.filter (fun a4 => (p : ℤ) ∣ a4), (g a4 : ℝ)) ≤
      ((A.filter (fun a4 => (p : ℤ) ∣ a4)).card : ℝ) * (2 * (a₆Bound : ℝ) / (p : ℝ) + 1) := by
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hAdvd_bound
  have hndvdsum : (∑ a4 ∈ A.filter (fun a4 => ¬ (p : ℤ) ∣ a4), (g a4 : ℝ)) ≤
      ((A.filter (fun a4 => ¬ (p : ℤ) ∣ a4)).card : ℝ) *
        (2 * ((2 * (a₆Bound : ℝ) + 1) / (p : ℝ) ^ 2 + 1)) := by
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hAndvd_bound
  have hcombinedR : (((A ×ˢ B).filter (fun q => 4 * q.1 ^ 3 + 27 * q.2 ^ 2 ≠ 0 ∧
          (p : ℤ) ^ 2 ∣ (4 * q.1 ^ 3 + 27 * q.2 ^ 2))).card : ℝ) ≤
      (∑ a4 ∈ A, (g a4 : ℝ)) := by
    exact_mod_cast hstep1
  rw [hsplit] at hcombinedR
  have key1 : (∑ a4 ∈ A.filter (fun a4 => (p : ℤ) ∣ a4), (g a4 : ℝ)) ≤
      (2 * (a₄Bound : ℝ) / (p : ℝ) + 1) * (2 * (a₆Bound : ℝ) / (p : ℝ) + 1) :=
    hdvdsum.trans (by gcongr)
  have key2 : (∑ a4 ∈ A.filter (fun a4 => ¬ (p : ℤ) ∣ a4), (g a4 : ℝ)) ≤
      (2 * (a₄Bound : ℝ) + 1) * (2 * ((2 * (a₆Bound : ℝ) + 1) / (p : ℝ) ^ 2 + 1)) :=
    hndvdsum.trans (by gcongr)
  linarith

/-- For `X ≥ 4`, there is at least one nonsingular curve of height `≤ X`: `N(X) ≥ 1`. -/
theorem Ncount_pos_of_ge_four (X : ℝ) (hX : 4 ≤ X) : 1 ≤ integralShortNFCount X := by
  have hcard := Ncount_eq_box_card X (by linarith : (0:ℝ) ≤ X)
  set S : Finset (ℤ × ℤ) :=
    (heightBox X).filter (fun q => 4 * q.1 ^ 3 + 27 * q.2 ^ 2 ≠ 0) with hS
  have hmem : ((-1, 0) : ℤ × ℤ) ∈ S := by
    have ha : (1 : ℤ) ≤ (WeierstrassCurve.a₄Bound X : ℤ) := by exact_mod_cast one_le_a₄Bound hX
    have hb : (0 : ℤ) ≤ (WeierstrassCurve.a₆Bound X : ℤ) := by positivity
    rw [hS, Finset.mem_filter, heightBox_def, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_Icc]
    exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by norm_num⟩
  have hcast : (integralShortNFCount X : ℕ) = S.card := by exact_mod_cast hcard
  rw [hcast]
  exact Finset.card_pos.mpr ⟨_, hmem⟩

/-- For `X ≥ 27`, `N(X)` is at least a third of the height-box size
`(2·a₄Bound+1)(2·a₆Bound+1)`. -/
theorem Ncount_ge (X : ℝ) (hX27 : 27 ≤ X) :
    (2*(WeierstrassCurve.a₄Bound X:ℝ)+1)*(2*(WeierstrassCurve.a₆Bound X:ℝ)+1) ≤
      3*(integralShortNFCount X : ℝ) := by
  have hsplit := Ncount_eq_boxSize_sub_singular (X := X) (by linarith : (0:ℝ) ≤ X)
  have hsing := singularCard_heightBox_le X
  have hLb3 : (3:ℝ) ≤ 2*(WeierstrassCurve.a₆Bound X:ℝ)+1 := by
    have : (1:ℝ) ≤ (WeierstrassCurve.a₆Bound X : ℝ) := by exact_mod_cast one_le_a₆Bound hX27
    linarith
  have hLa0 : (0:ℝ) ≤ (WeierstrassCurve.a₄Bound X : ℝ) := by positivity
  have hbox : boxSize X
      = (2*(WeierstrassCurve.a₄Bound X:ℝ)+1)*(2*(WeierstrassCurve.a₆Bound X:ℝ)+1) := rfl
  rw [hbox] at hsplit
  have hkey : 2*(2*(WeierstrassCurve.a₄Bound X:ℝ)+1) ≤
      (2/3)*((2*(WeierstrassCurve.a₄Bound X:ℝ)+1)*(2*(WeierstrassCurve.a₆Bound X:ℝ)+1)) := by
    nlinarith [hLb3, hLa0]
  linarith

/-- Let `p ≥ 5`, `A ≥ 3` and `B ≥ 5` be reals with `A³ = B²`, and let `a, b, N ≥ 1` satisfy
`A/4 ≤ a ≤ A`, `B/12 ≤ b ≤ B` and `(2a+1)(2b+1) ≤ 3N`. Then
`2(2a+1)((2b+1)/p² + 1) + (2a/p + 1)(2b/p + 1) ≤ 3456 N (1/p² + 1/(pA) + 1/B)`. -/
theorem boxEstimate_le {p a b A B N : ℝ} (hp : 5 ≤ p) (hA3 : 3 ≤ A) (hB5 : 5 ≤ B)
    (hAB : A * A * A = B * B) (haL : A / 4 ≤ a) (haU : a ≤ A) (hbL : B / 12 ≤ b)
    (hbU : b ≤ B) (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hN1 : 1 ≤ N)
    (hM3N : (2 * a + 1) * (2 * b + 1) ≤ 3 * N) :
    2 * (2 * a + 1) * ((2 * b + 1) / p ^ 2 + 1) + (2 * a / p + 1) * (2 * b / p + 1) ≤
      3456 * N * (1 / p ^ 2 + 1 / (p * A) + 1 / B) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hAp0 : (0 : ℝ) < A := by linarith
  have hBp0 : (0 : ℝ) < B := by linarith
  have hALEB : A ≤ B := by
    nlinarith [sq_nonneg (A - B), sq_nonneg (A + B), mul_nonneg hBp0.le hBp0.le, hA3]
  have hM4ab : 4 * a * b ≤ (2 * a + 1) * (2 * b + 1) := by nlinarith [ha1, hb1]
  have hABleM : A * B ≤ 12 * ((2 * a + 1) * (2 * b + 1)) := by
    nlinarith [mul_le_mul haL hbL (by linarith : (0 : ℝ) ≤ B / 12)
      (by linarith : (0 : ℝ) ≤ a), hM4ab, hAp0, hBp0]
  have hABN : A * B ≤ 36 * N := by nlinarith [hABleM, hM3N]
  have hAAN : A * A ≤ 36 * N := by nlinarith [hABN, hALEB, hAp0]
  have hBN : B ≤ 12 * N := by nlinarith [hABleM, hA3, hM3N, hBp0, hAp0]
  have hpA : (0 : ℝ) < p * A := by positivity
  rw [show 3456 * N * (1 / p ^ 2 + 1 / (p * A) + 1 / B) =
        3456 * N / p ^ 2 + 3456 * N / (p * A) + 3456 * N / B by field_simp,
    show 2 * (2 * a + 1) * ((2 * b + 1) / p ^ 2 + 1) + (2 * a / p + 1) * (2 * b / p + 1) =
        (2 * (2 * a + 1) * (2 * b + 1) + 4 * a * b) / p ^ 2 + (2 * a + 2 * b) / p +
          (2 * (2 * a + 1) + 1) by field_simp; ring]
  have hPnum : 2 * (2 * a + 1) * (2 * b + 1) + 4 * a * b ≤ 3456 * N := by
    nlinarith [hM3N, hN1, ha1, hb1]
  have hP : (2 * (2 * a + 1) * (2 * b + 1) + 4 * a * b) / p ^ 2 ≤ 3456 * N / p ^ 2 := by
    gcongr
  have hQnum : (2 * a + 2 * b) * A ≤ 3456 * N := by nlinarith [hAAN, hABN, haU, hbU, hAp0]
  have hQ : (2 * a + 2 * b) / p ≤ 3456 * N / (p * A) := by
    rw [div_le_div_iff₀ hp0 hpA]; nlinarith [hQnum, hp0, hAp0]
  have hR : 2 * (2 * a + 1) + 1 ≤ 3456 * N / B := by
    rw [le_div_iff₀ hBp0]; nlinarith [hABN, hBN, haU, hbU]
  linarith

/-- For a prime `p ≥ 5` and `X ≥ 4`,
`discBoxCount p X ≤ 3456 N(X) (1/p² + 1/(p X^{1/3}) + 1/X^{1/2})`. -/
theorem discBoxCount_le_aux (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (X : ℝ) (hX : 4 ≤ X) :
    (discBoxCount p X : ℝ) ≤
      3456 * (integralShortNFCount X : ℝ) *
        (1 / (p : ℝ) ^ 2 + 1 / ((p : ℝ) * X ^ (1 / 3 : ℝ)) + 1 / X ^ (1 / 2 : ℝ)) := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hpR : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (integralShortNFCount X : ℝ) := by
    exact_mod_cast Ncount_pos_of_ge_four X hX
  set a₄Bound := WeierstrassCurve.a₄Bound X with hLaDef
  set a₆Bound := WeierstrassCurve.a₆Bound X with hLbDef
  have hstep12 : (discBoxCount p X : ℝ) ≤
      2 * (2 * (a₄Bound : ℝ) + 1) * ((2 * (a₆Bound : ℝ) + 1) / (p : ℝ) ^ 2 + 1) +
        (2 * (a₄Bound : ℝ) / (p : ℝ) + 1) * (2 * (a₆Bound : ℝ) / (p : ℝ) + 1) := by
    have h1 := discBoxCount_le_finset p X hX0
    rw [heightBox_def] at h1
    exact le_trans (by exact_mod_cast h1) (filteredBox_card_le p hp hp5 a₄Bound a₆Bound)
  refine hstep12.trans ?_
  rcases lt_or_ge X 27 with hXlt | hX27
  · rw [show a₄Bound = 1 by rw [hLaDef]; exact a₄Bound_eq_one_of_lt hX hXlt,
      show a₆Bound = 0 by rw [hLbDef]; exact a₆Bound_eq_zero_of_lt hX0 hXlt]
    have hB0 : (0 : ℝ) < X ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hBlt6 : X ^ (1 / 2 : ℝ) < 6 := by
      calc X ^ (1 / 2 : ℝ) < (36 : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_lt_rpow hX0 (by linarith) (by norm_num)
        _ = 6 :=
            rpow_one_div_of_eq_pow 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdecay : (1 : ℝ) / 6 ≤
        1 / (p : ℝ) ^ 2 + 1 / ((p : ℝ) * X ^ (1 / 3 : ℝ)) + 1 / X ^ (1 / 2 : ℝ) := by
      have hB : 1 / (6 : ℝ) < 1 / X ^ (1 / 2 : ℝ) := by
        rw [div_lt_div_iff₀ (by norm_num) hB0]; nlinarith [hBlt6]
      have h1 : (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ 1 / ((p : ℝ) * X ^ (1 / 3 : ℝ)) := by positivity
      linarith
    have hrhs : (576 : ℝ) ≤
        3456 * (integralShortNFCount X : ℝ) *
          (1 / (p : ℝ) ^ 2 + 1 / ((p : ℝ) * X ^ (1 / 3 : ℝ)) + 1 / X ^ (1 / 2 : ℝ)) := by
      calc (576 : ℝ) = 3456 * 1 * (1 / 6) := by norm_num
        _ ≤ _ := by gcongr
    have hp2inv : (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [hpR]
    have hpinv : (1 : ℝ) / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; linarith
    rw [show 2 * (2 * ((1 : ℕ) : ℝ) + 1) * ((2 * ((0 : ℕ) : ℝ) + 1) / (p : ℝ) ^ 2 + 1) +
          (2 * ((1 : ℕ) : ℝ) / (p : ℝ) + 1) * (2 * ((0 : ℕ) : ℝ) / (p : ℝ) + 1) =
        6 * (1 / (p : ℝ) ^ 2) + 6 + 2 * (1 / (p : ℝ)) + 1 by push_cast; field_simp; ring]
    linarith
  · have hA3 : 3 ≤ X ^ (1 / 3 : ℝ) := by
      calc (3 : ℝ) = (27 : ℝ) ^ (1 / 3 : ℝ) :=
            (rpow_one_div_of_eq_pow 3 (by norm_num) (by norm_num) (by norm_num)
              (by norm_num)).symm
        _ ≤ X ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) hX27 (by norm_num)
    have hB5 : 5 ≤ X ^ (1 / 2 : ℝ) := by
      calc (5 : ℝ) = (25 : ℝ) ^ (1 / 2 : ℝ) :=
            (rpow_one_div_of_eq_pow 2 (by norm_num) (by norm_num) (by norm_num)
              (by norm_num)).symm
        _ ≤ X ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
    have hAB : X ^ (1 / 3 : ℝ) * X ^ (1 / 3 : ℝ) * X ^ (1 / 3 : ℝ) =
        X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) := by
      rw [show X ^ (1 / 3 : ℝ) * X ^ (1 / 3 : ℝ) * X ^ (1 / 3 : ℝ) = (X ^ (1 / 3 : ℝ)) ^ (3 : ℕ)
          by ring,
        show X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) = (X ^ (1 / 2 : ℝ)) ^ (2 : ℕ) by ring,
        ← Real.rpow_natCast (X ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hX0,
        ← Real.rpow_natCast (X ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hX0]
      norm_num
    exact boxEstimate_le hpR hA3 hB5 hAB (rpow_div_le_a₄Bound hX) (a₄Bound_le_rpow hX0)
      (rpow_div_le_a₆Bound hX27) (a₆Bound_le_rpow hX0) (by exact_mod_cast one_le_a₄Bound hX)
      (by exact_mod_cast one_le_a₆Bound hX27) hN1 (Ncount_ge X hX27)

/-- There is a uniform `C₁ > 0` such that for every prime `p ≥ 5` and every `X ≥ 4`,

  `#{(a₄, a₆) : Ht ≤ X, 4a₄³+27a₆² ≠ 0, p² ∣ 4a₄³+27a₆²}`
    `≤ C₁ N(X) (1/p² + 1/(p X^{1/3}) + 1/X^{1/2})`. -/
theorem discBoxCount_le :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : ℝ), 4 ≤ X →
        (discBoxCount p X : ℝ) ≤
          C₁ * (integralShortNFCount X : ℝ) *
            (1 / (p : ℝ) ^ 2 + 1 / ((p : ℝ) * X ^ (1 / 3 : ℝ)) + 1 / X ^ (1 / 2 : ℝ)) :=
  ⟨3456, by norm_num, discBoxCount_le_aux⟩

/-- For a prime `p ≥ 5`, the exceptional count `exceptionalCount p X` is at most the congruence
count `discBoxCount p X`. -/
theorem exceptional_le_discBoxCount (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (X : ℝ) :
    exceptionalCount p X ≤ discBoxCount p X := by
  have hp : p.Prime := Fact.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpnd16 : ¬ (p : ℤ) ∣ (16 : ℤ) :=
    not_dvd_of_eq_pow hp 2 4 (by norm_num) (by omega) (by norm_num)
  have hcop : IsCoprime ((p : ℤ) ^ 2) (-16 : ℤ) :=
    isCoprime_sq_of_not_dvd hp fun h => hpnd16 (dvd_neg.mp h)
  have hsub :
      {q : ℤ × ℤ |
          (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ q ∈ integralShortNFFamily ∧
          ((tauZ p q.1 q.2).kodairaSymbol, (tauZ p q.1 q.2).tamagawaNumber) ∉ K0} ⊆
        {q : ℤ × ℤ |
          (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ 4 * q.1 ^ 3 + 27 * q.2 ^ 2 ≠ 0 ∧
          (p : ℤ) ^ 2 ∣ (4 * q.1 ^ 3 + 27 * q.2 ^ 2)} := by
    intro q hq
    obtain ⟨hh, hfam, hnotK0⟩ := hq
    have hne : 4 * q.1 ^ 3 + 27 * q.2 ^ 2 ≠ 0 :=
      (ofShortNF_Δ_ne_zero_iff q.1 q.2).mp hfam
    refine ⟨hh, hne, ?_⟩
    have hp2disc : (p : ℤ) ^ 2 ∣ (ofShortNF q.1 q.2).Δ := by
      by_contra hcon
      exact hnotK0 (tauZ_mem_K0_of_not_sq_dvd p q.1 q.2 (by exact_mod_cast hcon))
    rw [ofShortNF_Δ] at hp2disc
    exact hcop.dvd_of_dvd_mul_left hp2disc
  have hfin :
      {q : ℤ × ℤ |
          (integralShortNFHeight q.1 q.2 : ℝ) ≤ X ∧ 4 * q.1 ^ 3 + 27 * q.2 ^ 2 ≠ 0 ∧
          (p : ℤ) ^ 2 ∣ (4 * q.1 ^ 3 + 27 * q.2 ^ 2)}.Finite := by
    by_cases hX : (0 : ℝ) ≤ X
    · refine Set.Finite.subset (Finset.finite_toSet (heightBox X)) ?_
      intro q hq
      exact Finset.mem_coe.mpr ((mem_heightBox_iff hX q).mpr hq.1)
    · refine Set.Finite.subset Set.finite_empty ?_
      intro q hq
      have h0 : (0 : ℤ) ≤ integralShortNFHeight q.1 q.2 := by
        rw [integralShortNFHeight_eq]; exact le_max_of_le_left (by positivity)
      exact absurd (le_trans (by exact_mod_cast h0) hq.1) hX
  exact Set.ncard_le_ncard hsub hfin

/-! ## Main statement -/

/-- There is a uniform constant `C > 0` such that for every prime `p ≥ 5` and every real `X ≥ 4`,
the proportion of nonsingular height-`≤ X` short Weierstrass curves whose local reduction type
`τ_p` at `p` lies outside the trivial set `𝒦₀ = {(I₀,1), (I₁,1)}` is at most
`C (1/p² + 1/(p X^{1/3}) + 1/X^{1/2})`. -/
@[bsd_tamagawa "T030a"]
theorem exceptional_ratio_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
        ∀ (X : ℝ), 4 ≤ X →
          (exceptionalCount p X : ℝ) / (integralShortNFCount X : ℝ) ≤
            C * (1 / (p : ℝ) ^ 2 + 1 / ((p : ℝ) * X ^ (1 / 3 : ℝ)) +
              1 / X ^ (1 / 2 : ℝ)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := discBoxCount_le
  refine ⟨C₁, hC₁pos, fun p hpf hp5 X hX => ?_⟩
  set S : ℝ := 1 / (p : ℝ) ^ 2 + 1 / ((p : ℝ) * X ^ (1 / 3 : ℝ)) + 1 / X ^ (1 / 2 : ℝ)
  have hNposR : (0 : ℝ) < (integralShortNFCount X : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (Ncount_pos_of_ge_four X hX)
  have h1 : (exceptionalCount p X : ℝ) ≤ (discBoxCount p X : ℝ) := by
    exact_mod_cast exceptional_le_discBoxCount p hp5 X
  have h2 : (discBoxCount p X : ℝ) ≤ C₁ * (integralShortNFCount X : ℝ) * S :=
    hC₁ p hpf.out hp5 X hX
  rw [div_le_iff₀ hNposR]
  linarith

end ShortWeierstrassReductionStatistics
