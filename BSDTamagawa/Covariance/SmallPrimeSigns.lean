/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Covariance.Negative
public import BSDTamagawa.NumberTheory.SmallPrimeHeadBound
public import BSDTamagawa.NumberTheory.SmallPrimeStratum

/-!
# The local covariance `C_q(2, 3)` at the small primes

For `q ∈ {2, 3}` and `t ≥ 5` the local density satisfies the tail bound

  `δ_q(t) ≤ 2 q^{-(t+4)}`.

The split multiplicative stratum of level `t` at `q = 2` lies in the union over `s` of the loci
`v₂(a₆) = 6s + 1`, `v₂(Δ) = t + 12s + 12`, and at `q = 3` in the loci `v₃(a₆) = 6s + 3`,
`v₃(Δ) = t + 12s + 12`. Two solutions `b, b₀` of a quadratic congruence `p^{s+k} ∣ c + p^s u b²`
satisfy `p^k ∣ (b - b₀)(b + b₀)`, and since the two factors differ by `2b₀`, a cap on `v_p(b₀)`
forces almost all of the divisibility into one factor. This gives a bound at the full rate
`q^{-t}`, summable over `s`.

With this bound the cross-moment is at most `(2/q⁴) · q⁶/(q⁶ - 1)²`, while
`μ_{q,2} μ_{q,3} ≥ 1/(6q⁵)`; since `12q⁷ < (q⁶ - 1)²` at `q = 2, 3`, the local covariance
`C_q(2, 3)` is negative. Together with the primes `q ≥ 5`, `C_q(2, 3) < 0` at every prime.

## Main results

* `PadicInt.volume_setOf_pow_dvd_add_sq_le_of_not_dvd`: the mass of a quadratic congruence class
  with a cap on the valuation.
* `WeierstrassCurve.δ_le_two_mul_inv_pow_add_four`: `δ_q(t) ≤ 2 q^{-(t+4)}` for `q ∈ {2, 3}` and
  `t ≥ 5`.
* `WeierstrassCurve.localCov_two_three_neg_of_prime`: `C_q(2, 3) < 0` at every prime `q`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

/-! ### The ultrametric split under a cap on `v_p(x - y)` -/

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- If `p^m ∣ xy` and `p^{n+1} ∤ x - y`, then `p^j` divides `x` or `y` for every `j` with
`j + n ≤ m`. -/
theorem pow_dvd_or_pow_dvd_of_pow_dvd_mul_of_not_dvd_sub {j n m : ℕ} (hj : j + n ≤ m)
    {x y : ℤ_[p]} (h : (p : ℤ_[p]) ^ m ∣ x * y)
    (hxy : ¬ (p : ℤ_[p]) ^ (n + 1) ∣ x - y) :
    (p : ℤ_[p]) ^ j ∣ x ∨ (p : ℤ_[p]) ^ j ∣ y := by
  by_contra hcon
  rw [not_or, pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity, not_le, not_le] at hcon
  obtain ⟨hx, hy⟩ := hcon
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hx.ne_top
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hy.ne_top
  rw [pow_dvd_iff_le_emultiplicity, emultiplicity_mul prime_p, ← ha, ← hb] at h
  rw [← ha] at hx
  rw [← hb] at hy
  have hxn : a < j := by exact_mod_cast hx
  have hyn : b < j := by exact_mod_cast hy
  have hmn : m ≤ a + b := by exact_mod_cast h
  have hmin : a ≤ n ∨ b ≤ n := by
    by_contra hc
    rw [not_or, not_le, not_le] at hc
    refine hxy (dvd_sub ?_ ?_)
    · refine pow_dvd_of_le_emultiplicity ?_
      rw [← ha]
      exact_mod_cast Nat.succ_le_of_lt hc.1
    · refine pow_dvd_of_le_emultiplicity ?_
      rw [← hb]
      exact_mod_cast Nat.succ_le_of_lt hc.2
  omega

/-- If `p^{m+1} ∤ b`, then `p^{m+2} ∤ 2b`. -/
theorem not_pow_dvd_two_mul {m : ℕ} {b : ℤ_[p]} (h : ¬ (p : ℤ_[p]) ^ (m + 1) ∣ b) :
    ¬ (p : ℤ_[p]) ^ (m + 2) ∣ 2 * b := by
  intro hd
  refine h ?_
  rcases eq_or_ne p 2 with hp2 | hp2
  · subst hp2
    have h2 : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by push_cast; ring
    rw [h2, show m + 2 = 1 + (m + 1) from by ring, pow_add, pow_one] at hd
    exact (mul_dvd_mul_iff_left (prime_p (p := 2)).ne_zero).mp hd
  · have hnd : ¬ p ∣ 2 := by
      intro hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd)
    have hu : IsUnit (2 : ℤ_[p]) := by
      have h := isUnit_natCast_of_not_dvd (p := p) (n := 2) hnd
      simpa using h
    exact dvd_trans (pow_dvd_pow _ (by omega)) (hu.dvd_mul_left.mp hd)

/-- For a unit `u`, any `c`, and any `j` with `j + (m + 1) ≤ k`,

  `μ_p {b | p^{m+1} ∤ b ∧ p^{s+k} ∣ c + p^s u b²} ≤ 2 p^{-j}`. -/
theorem volume_setOf_pow_dvd_add_sq_le_of_not_dvd {s k m j : ℕ} (hj : j + (m + 1) ≤ k) {u c : ℤ_[p]}
    (hu : IsUnit u) :
    (volume : Measure ℤ_[p])
        {b : ℤ_[p] | ¬ (p : ℤ_[p]) ^ (m + 1) ∣ b ∧
          (p : ℤ_[p]) ^ (s + k) ∣ c + (p : ℤ_[p]) ^ s * u * b ^ 2}
      ≤ 2 * ((p : ℝ≥0∞)⁻¹) ^ j := by
  rcases eq_empty_or_nonempty {b : ℤ_[p] | ¬ (p : ℤ_[p]) ^ (m + 1) ∣ b ∧
      (p : ℤ_[p]) ^ (s + k) ∣ c + (p : ℤ_[p]) ^ s * u * b ^ 2} with hE | ⟨b₀, hb₀⟩
  · rw [hE]; simp
  obtain ⟨hb₀cap, hb₀'⟩ := hb₀
  have hps : ((p : ℤ_[p]) ^ s) ≠ 0 := pow_ne_zero s prime_p.ne_zero
  have hsub : {b : ℤ_[p] | ¬ (p : ℤ_[p]) ^ (m + 1) ∣ b ∧
        (p : ℤ_[p]) ^ (s + k) ∣ c + (p : ℤ_[p]) ^ s * u * b ^ 2}
      ⊆ (toZModPow j ⁻¹' {toZModPow j b₀}) ∪ (toZModPow j ⁻¹' {toZModPow j (-b₀)}) := by
    intro b hb
    obtain ⟨-, hb'⟩ := hb
    have hd : (p : ℤ_[p]) ^ s * (p : ℤ_[p]) ^ k
        ∣ (p : ℤ_[p]) ^ s * (u * ((b - b₀) * (b + b₀))) := by
      have hds := dvd_sub hb' hb₀'
      rw [show c + (p : ℤ_[p]) ^ s * u * b ^ 2 - (c + (p : ℤ_[p]) ^ s * u * b₀ ^ 2)
        = (p : ℤ_[p]) ^ s * (u * ((b - b₀) * (b + b₀))) from by ring] at hds
      rwa [← pow_add]
    have hk : (p : ℤ_[p]) ^ k ∣ (b - b₀) * (b + b₀) :=
      hu.dvd_mul_left.mp ((mul_dvd_mul_iff_left hps).mp hd)
    have hne : ¬ (p : ℤ_[p]) ^ (m + 1 + 1) ∣ (b - b₀) - (b + b₀) := by
      rw [show (b - b₀) - (b + b₀) = -(2 * b₀) from by ring, dvd_neg,
        show m + 1 + 1 = m + 2 from rfl]
      exact not_pow_dvd_two_mul hb₀cap
    rcases pow_dvd_or_pow_dvd_of_pow_dvd_mul_of_not_dvd_sub (n := m + 1) hj hk hne with hle | hle
    · exact Or.inl (toZModPow_eq_iff_pow_dvd_sub.mpr hle)
    · refine Or.inr (toZModPow_eq_iff_pow_dvd_sub.mpr ?_)
      rwa [sub_neg_eq_add]
  calc (volume : Measure ℤ_[p]) {b : ℤ_[p] | ¬ (p : ℤ_[p]) ^ (m + 1) ∣ b ∧
        (p : ℤ_[p]) ^ (s + k) ∣ c + (p : ℤ_[p]) ^ s * u * b ^ 2}
      ≤ volume ((toZModPow j ⁻¹' {toZModPow j b₀})
          ∪ (toZModPow j ⁻¹' {toZModPow j (-b₀)})) := measure_mono hsub
    _ ≤ volume (toZModPow j ⁻¹' {toZModPow j b₀})
          + volume (toZModPow j ⁻¹' {toZModPow j (-b₀)}) := measure_union_le _ _
    _ = 2 * ((p : ℝ≥0∞)⁻¹) ^ j := by
        rw [volume_preimage_toZModPow, volume_preimage_toZModPow, ENNReal.inv_pow]
        ring

end PadicInt

/-! ### A geometric sum -/

namespace WeierstrassCurve

open BSDTamagawa BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

/-- `(1 - r)⁻¹ ≤ 2` for `r ≤ 2⁻¹` in `ℝ≥0∞`. -/
theorem inv_one_sub_le_two {r : ℝ≥0∞} (hr : r ≤ 2⁻¹) : (1 - r)⁻¹ ≤ 2 := by
  have h : (2 : ℝ≥0∞)⁻¹ ≤ 1 - r :=
    calc (2 : ℝ≥0∞)⁻¹ = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
      _ ≤ 1 - r := tsub_le_tsub_left hr 1
  calc (1 - r)⁻¹ ≤ ((2 : ℝ≥0∞)⁻¹)⁻¹ := ENNReal.inv_le_inv.2 h
    _ = 2 := inv_inv 2

/-- `∑'_s 2 r^{n+1+s} ≤ 2 r^n` for `r ≤ 2⁻¹` in `ℝ≥0∞`. -/
theorem tsum_two_mul_pow_le {r : ℝ≥0∞} (hr : r ≤ 2⁻¹) (n : ℕ) :
    (∑' s : ℕ, 2 * r ^ (n + 1 + s)) ≤ 2 * r ^ n := by
  have hfun : (fun s : ℕ => 2 * r ^ (n + 1 + s)) = fun s : ℕ => (2 * r ^ (n + 1)) * r ^ s :=
    funext fun s => by rw [pow_add]; ring
  have hsum : (∑' s : ℕ, 2 * r ^ (n + 1 + s)) = 2 * r ^ (n + 1) * (1 - r)⁻¹ := by
    rw [hfun, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have h2 : (2 : ℝ≥0∞) * 2 * 2⁻¹ = 2 := by
    rw [mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]
  rw [hsum]
  calc 2 * r ^ (n + 1) * (1 - r)⁻¹ ≤ 2 * r ^ (n + 1) * 2 :=
        mul_le_mul' le_rfl (inv_one_sub_le_two hr)
    _ = 2 * 2 * r * r ^ n := by rw [pow_succ]; ring
    _ ≤ 2 * 2 * 2⁻¹ * r ^ n := by gcongr
    _ = 2 * r ^ n := by rw [h2]

/-! ### The full-rate tail bound at `p = 2` and `p = 3` -/

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- The locus of pairs `(a₄, a₆)` with `p^{m+1} ∤ a₆`. -/
def notDvdSndLocus (m : ℕ) : Set (ℤ_[p] × ℤ_[p]) := {x | ¬ (p : ℤ_[p]) ^ (m + 1) ∣ x.2}

/-- The locus `{p^{m+1} ∤ a₆}` is measurable. -/
theorem measurableSet_notDvdSndLocus (m : ℕ) : MeasurableSet (notDvdSndLocus p m) := by
  have h : notDvdSndLocus p m
      = (Prod.snd ⁻¹' ((Ideal.span {(p : ℤ_[p]) ^ (m + 1)} : Ideal ℤ_[p]) : Set ℤ_[p]))ᶜ := by
    ext x
    simp [notDvdSndLocus, Ideal.mem_span_singleton]
  rw [h]
  exact (measurable_snd (PadicInt.measurableSet_span_pPow (m + 1))).compl

/-- If `-432 = p^s u` with `u` a unit then, for every `j` with `j + (m + 1) ≤ k`,

  `μ_p ({v_p(Δ) ≥ s + k} ∩ {p^{m+1} ∤ a₆}) ≤ 2 p^{-j}`. -/
theorem volume_dvdΔLocus_inter_notDvdSndLocus_le {s k m j : ℕ} (hj : j + (m + 1) ≤ k) {u : ℤ_[p]}
    (hu : IsUnit u) (hpu : (p : ℤ_[p]) ^ s * u = -432) :
    (volume : Measure (ℤ_[p] × ℤ_[p])) (dvdΔLocus p (s + k) ∩ notDvdSndLocus p m)
      ≤ 2 * ((p : ℝ≥0∞)⁻¹) ^ j := by
  have hslice : ∀ a : ℤ_[p], (volume : Measure ℤ_[p])
      (Prod.mk a ⁻¹' (dvdΔLocus p (s + k) ∩ notDvdSndLocus p m))
      ≤ 2 * ((p : ℝ≥0∞)⁻¹) ^ j := by
    intro a
    refine le_trans (measure_mono ?_)
      (PadicInt.volume_setOf_pow_dvd_add_sq_le_of_not_dvd (s := s) (k := k) (m := m) (j := j)
        (c := -64 * a ^ 3) hj hu)
    intro b hb
    obtain ⟨hbΔ, hbcap⟩ := hb
    refine ⟨hbcap, ?_⟩
    have hb' : (p : ℤ_[p]) ^ (s + k) ∣ (ofShortNF a b).Δ := hbΔ
    rw [ofShortNF_Δ] at hb'
    change (p : ℤ_[p]) ^ (s + k) ∣ -64 * a ^ 3 + (p : ℤ_[p]) ^ s * u * b ^ 2
    rwa [show -64 * a ^ 3 + (p : ℤ_[p]) ^ s * u * b ^ 2 = -16 * (4 * a ^ 3 + 27 * b ^ 2) from by
      rw [hpu]; ring]
  calc (volume : Measure (ℤ_[p] × ℤ_[p])) (dvdΔLocus p (s + k) ∩ notDvdSndLocus p m)
      = ((volume : Measure ℤ_[p]).prod (volume : Measure ℤ_[p]))
          (dvdΔLocus p (s + k) ∩ notDvdSndLocus p m) := by rw [← Measure.volume_eq_prod]
    _ ≤ ∫⁻ a, (volume : Measure ℤ_[p])
          (Prod.mk a ⁻¹' (dvdΔLocus p (s + k) ∩ notDvdSndLocus p m)) ∂(volume : Measure ℤ_[p]) :=
        Measure.prod_apply_le ((measurableSet_dvdΔLocus (s + k)).inter
          (measurableSet_notDvdSndLocus m))
    _ ≤ ∫⁻ _ : ℤ_[p], 2 * ((p : ℝ≥0∞)⁻¹) ^ j ∂(volume : Measure ℤ_[p]) := lintegral_mono hslice
    _ = 2 * ((p : ℝ≥0∞)⁻¹) ^ j := by rw [lintegral_const, measure_univ, mul_one]

/-- If the split multiplicative stratum of level `t ≥ 5` is covered by the loci
`{v_p(Δ) ≥ t + 12s + 12} ∩ {p^{6s+c+1} ∤ a₆}`, and `-432 = p^{sh} u` with `u` a unit, `sh ≤ 4` and
`sh + c ≤ 6`, then `δ_p(t) ≤ 2 p^{-(t+4)}`. -/
theorem δ_le_two_mul_inv_pow_add_four_of_cover {t c sh : ℕ} (ht : 5 ≤ t) (hsh : sh ≤ 4)
    (hc : sh + c ≤ 6) {u : ℤ_[p]} (hu : IsUnit u) (hpu : (p : ℤ_[p]) ^ sh * u = -432)
    (hcov : stratFibre p (KodairaSymbol.I t, t)
      ⊆ ⋃ s : ℕ, (dvdΔLocus p (t + 12 * s + 12) ∩ notDvdSndLocus p (6 * s + c))) :
    δ p t ≤ 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 4) := by
  have hr : ((p : ℝ≥0∞))⁻¹ ≤ 2⁻¹ := by
    refine ENNReal.inv_le_inv.2 ?_
    exact_mod_cast (Fact.out : p.Prime).two_le
  have hstep : ∀ s : ℕ, (volume : Measure (ℤ_[p] × ℤ_[p]))
      (dvdΔLocus p (t + 12 * s + 12) ∩ notDvdSndLocus p (6 * s + c))
        ≤ 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 4 + 1 + s) := by
    intro s
    have hk : sh + (t + 12 * s + 12 - sh) = t + 12 * s + 12 := by omega
    have hb := volume_dvdΔLocus_inter_notDvdSndLocus_le (p := p) (s := sh)
      (k := t + 12 * s + 12 - sh) (m := 6 * s + c) (j := t + 4 + 1 + s) (by omega) hu hpu
    rwa [hk] at hb
  have hδ : δ p t = volume (stratFibre p (KodairaSymbol.I t, t)) := by
    rw [δ_eq_deltaP_I ht, volume_stratFibre]
  rw [hδ]
  calc volume (stratFibre p (KodairaSymbol.I t, t))
      ≤ volume (⋃ s : ℕ, (dvdΔLocus p (t + 12 * s + 12) ∩ notDvdSndLocus p (6 * s + c))) :=
        measure_mono hcov
    _ ≤ ∑' s : ℕ, volume (dvdΔLocus p (t + 12 * s + 12) ∩ notDvdSndLocus p (6 * s + c)) :=
        measure_iUnion_le _
    _ ≤ ∑' s : ℕ, 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 4 + 1 + s) := ENNReal.tsum_le_tsum hstep
    _ ≤ 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 4) := tsum_two_mul_pow_le hr (t + 4)

/-- `δ_2(t) ≤ 2·2^{-(t+4)}` for every `t ≥ 5`. -/
theorem δ_le_two_mul_inv_pow_add_four_at_two (hp2 : p = 2) {t : ℕ} (ht : 5 ≤ t) :
    δ p t ≤ 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 4) := by
  have hu : IsUnit (-27 : ℤ_[p]) := by
    have h := PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 27) (by rw [hp2]; norm_num)
    simpa using h.neg
  refine δ_le_two_mul_inv_pow_add_four_of_cover (c := 1) (sh := 4) ht (by norm_num) (by norm_num)
    hu (by subst hp2; push_cast; norm_num) ?_
  intro x hx
  obtain ⟨s, -, h6, hΔ⟩ := exists_emultiplicity_of_mem_stratFibre_two hp2 ht hx
  refine Set.mem_iUnion.2 ⟨s, ?_, ?_⟩
  · change (p : ℤ_[p]) ^ (t + 12 * s + 12) ∣ (ofShortNF x.1 x.2).Δ
    exact pow_dvd_of_le_emultiplicity (by rw [hΔ])
  · change ¬ (p : ℤ_[p]) ^ (6 * s + 1 + 1) ∣ x.2
    intro hd
    have hle := le_emultiplicity_of_pow_dvd hd
    rw [h6] at hle
    have : (6 * s + 1 + 1 : ℕ) ≤ 6 * s + 1 := by exact_mod_cast hle
    omega

/-- `δ_3(t) ≤ 2·3^{-(t+4)}` for every `t ≥ 5`. -/
theorem δ_le_two_mul_inv_pow_add_four_at_three (hp3 : p = 3) {t : ℕ} (ht : 5 ≤ t) :
    δ p t ≤ 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 4) := by
  have hu : IsUnit (-16 : ℤ_[p]) := by
    have h := PadicInt.isUnit_natCast_of_not_dvd (p := p) (n := 16) (by rw [hp3]; norm_num)
    simpa using h.neg
  refine δ_le_two_mul_inv_pow_add_four_of_cover (c := 3) (sh := 3) ht (by norm_num) (by norm_num)
    hu (by subst hp3; push_cast; norm_num) ?_
  intro x hx
  obtain ⟨s, -, h6, hΔ⟩ := exists_emultiplicity_of_mem_stratFibre_three hp3 ht hx
  refine Set.mem_iUnion.2 ⟨s, ?_, ?_⟩
  · change (p : ℤ_[p]) ^ (t + 12 * s + 12) ∣ (ofShortNF x.1 x.2).Δ
    exact pow_dvd_of_le_emultiplicity (by rw [hΔ])
  · change ¬ (p : ℤ_[p]) ^ (6 * s + 3 + 1) ∣ x.2
    intro hd
    have hle := le_emultiplicity_of_pow_dvd hd
    rw [h6] at hle
    have : (6 * s + 3 + 1 : ℕ) ≤ 6 * s + 3 := by exact_mod_cast hle
    omega

/-- The two small primes at once: `δ_q(t) ≤ 2 q^{-(t+4)}` for `q ∈ {2, 3}` and `t ≥ 5`. -/
theorem δ_le_two_mul_inv_pow_add_four (hp : p = 2 ∨ p = 3) {t : ℕ} (ht : 5 ≤ t) :
    δ p t ≤ 2 * ((p : ℝ≥0∞)⁻¹) ^ (t + 4) := by
  rcases hp with h | h
  · exact δ_le_two_mul_inv_pow_add_four_at_two h ht
  · exact δ_le_two_mul_inv_pow_add_four_at_three h ht

/-- `δ_q(t) ≤ 2 q^{-(t+4)}` in `ℝ`, for `q ∈ {2, 3}` and `t ≥ 5`. -/
theorem toReal_δ_le_two_mul_inv_pow_add_four (hp : p = 2 ∨ p = 3) {t : ℕ} (ht : 5 ≤ t) :
    (δ p t).toReal ≤ 2 * ((p : ℝ)⁻¹) ^ (t + 4) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hinv : (p : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp [hp0]
  have hne : (2 : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ (t + 4) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top hinv)
  have h := ENNReal.toReal_mono hne (δ_le_two_mul_inv_pow_add_four hp ht)
  simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv] using h

/-! ### The cross-moment at `(ℓ, ℓ') = (2, 3)` -/

/-- For `q ∈ {2, 3}`, the cross summand `δ_q(t) v_2(t) v_3(t)` is at most
`2q^{-4} · BivariateValuationSum.summand 2 3 q t`. -/
theorem crossValuationTerm_two_three_le_summand (hp : p = 2 ∨ p = 3) (t : ℕ) :
    crossValuationTerm p 2 3 t
      ≤ 2 / (p : ℝ) ^ 4 * BivariateValuationSum.summand 2 3 (p : ℝ) t := by
  rcases lt_or_ge t 5 with ht | ht
  · rw [crossValuationTerm_eq_zero_of_lt_five p Nat.prime_two Nat.prime_three (by norm_num) ht,
      BivariateValuationSum.summand, ite_eq_right (by omega), mul_zero]
  · have hz : (p : ℝ) ^ (-(t : ℤ)) = ((p : ℝ)⁻¹) ^ t := by rw [zpow_neg, zpow_natCast, inv_pow]
    calc crossValuationTerm p 2 3 t
        = (δ p t).toReal * ((padicValNat 2 t : ℝ) * (padicValNat 3 t : ℝ)) := by
          rw [crossValuationTerm, mul_assoc]
      _ ≤ 2 * ((p : ℝ)⁻¹) ^ (t + 4) * ((padicValNat 2 t : ℝ) * (padicValNat 3 t : ℝ)) :=
          mul_le_mul_of_nonneg_right (toReal_δ_le_two_mul_inv_pow_add_four hp ht)
            (by positivity)
      _ = 2 / (p : ℝ) ^ 4 * BivariateValuationSum.summand 2 3 (p : ℝ) t := by
          rw [BivariateValuationSum.summand, ite_eq_left ht, hz, pow_add,
            show (2 : ℝ) / (p : ℝ) ^ 4 = 2 * ((p : ℝ)⁻¹) ^ 4 by rw [inv_pow, div_eq_mul_inv]]
          ring

/-- For `q ∈ {2, 3}`, `∑_t δ_q(t) v_2(t) v_3(t) ≤ (2/q⁴) · q⁶/(q⁶ - 1)²`. -/
theorem crossValuationMoment_two_three_le (hp : p = 2 ∨ p = 3) :
    crossValuationMoment p 2 3 ≤ 2 / (p : ℝ) ^ 4 * ((p : ℝ) ^ 6 / ((p : ℝ) ^ 6 - 1) ^ 2) := by
  have hbound :=
    BSDTamagawa.BivariateValuationSum.main_theorem 2 3 Nat.prime_two Nat.prime_three (by norm_num)
      (p : ℝ) two_le_cast_prime
  rw [← Nat.cast_mul, zpow_neg_div_one_sub_sq (P := (p : ℝ)) two_le_cast_prime (by norm_num)]
    at hbound
  have hsum := summable_crossValuationTerm' (p := p) Nat.prime_two Nat.prime_three (by norm_num)
  have hmaj : Summable fun t : ℕ =>
      2 / (p : ℝ) ^ 4 * BivariateValuationSum.summand 2 3 (p : ℝ) t :=
    (BivariateValuationSum.summand_summable 2 3 Nat.prime_two Nat.prime_three (by norm_num)
      (p : ℝ) two_le_cast_prime).mul_left _
  calc crossValuationMoment p 2 3
      ≤ ∑' t : ℕ, 2 / (p : ℝ) ^ 4 * BivariateValuationSum.summand 2 3 (p : ℝ) t :=
        hsum.tsum_le_tsum (crossValuationTerm_two_three_le_summand hp) hmaj
    _ = 2 / (p : ℝ) ^ 4 * ∑' t : ℕ, BivariateValuationSum.summand 2 3 (p : ℝ) t := tsum_mul_left
    _ ≤ 2 / (p : ℝ) ^ 4 * ((p : ℝ) ^ (2 * 3) / ((p : ℝ) ^ (2 * 3) - 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 2 / (p : ℝ) ^ 4 * ((p : ℝ) ^ 6 / ((p : ℝ) ^ 6 - 1) ^ 2) := by norm_num

/-! ### Lower bounds on the marginal moments -/

/-- `A_{q,r} ≤ μ_{q,r}` for a prime `r`. -/
theorem toReal_headSum_le_valuationMoment' {r : ℕ} (hr : r.Prime) :
    (headSum p r).toReal ≤ valuationMoment p r := by
  rw [headSum, ENNReal.toReal_sum fun t _ => δ_mul_natCast_ne_top p t _]
  calc ∑ t ∈ Finset.Icc 1 4, (δ p t * (padicValNat r t : ℝ≥0∞)).toReal
      = ∑ t ∈ Finset.Icc 1 4, valuationTerm p r t :=
        Finset.sum_congr rfl fun t _ => (valuationTerm_eq_toReal p r t).symm
    _ ≤ ∑' t : ℕ, valuationTerm p r t :=
        (summable_valuationTerm' (p := p) hr).sum_le_tsum _ fun t _ => valuationTerm_nonneg p r t

/-- `1/(2q²) ≤ μ_{q,2}` at every prime `q`. -/
theorem inv_two_mul_sq_le_valuationMoment_two' : 1 / (2 * (p : ℝ) ^ 2) ≤ valuationMoment p 2 := by
  have hfin : (1 : ℝ≥0∞) / (2 * (p : ℝ≥0∞) ^ 2) ≠ ⊤ :=
    (ENNReal.div_lt_top ENNReal.one_ne_top (mul_ne_zero two_ne_zero
      (pow_ne_zero 2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)))).ne
  have h1 := (ENNReal.toReal_le_toReal hfin (headSum_ne_top 2)).2
    (inv_two_mul_sq_le_headSum_two_of_prime (p := p))
  have h2 : ((1 : ℝ≥0∞) / (2 * (p : ℝ≥0∞) ^ 2)).toReal = 1 / (2 * (p : ℝ) ^ 2) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    norm_num
  rw [h2] at h1
  exact h1.trans (toReal_headSum_le_valuationMoment' Nat.prime_two)

/-- `1/(3q³) ≤ μ_{q,3}` at every prime `q`. -/
theorem inv_three_mul_cube_le_valuationMoment_three' :
    1 / (3 * (p : ℝ) ^ 3) ≤ valuationMoment p 3 := by
  have hfin : (1 : ℝ≥0∞) / (3 * (p : ℝ≥0∞) ^ 3) ≠ ⊤ :=
    (ENNReal.div_lt_top ENNReal.one_ne_top (mul_ne_zero three_ne_zero
      (pow_ne_zero 3 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)))).ne
  have h1 := (ENNReal.toReal_le_toReal hfin (headSum_ne_top 3)).2
    (inv_three_mul_cube_le_headSum_three_of_prime (p := p))
  have h2 : ((1 : ℝ≥0∞) / (3 * (p : ℝ≥0∞) ^ 3)).toReal = 1 / (3 * (p : ℝ) ^ 3) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    norm_num
  rw [h2] at h1
  exact h1.trans (toReal_headSum_le_valuationMoment' Nat.prime_three)

/-! ### Negativity of `C_q(2, 3)` -/

/-- `12 P⁷ < (P⁶ - 1)²` for `P = 2` and `P = 3`. -/
theorem twelve_mul_pow_seven_lt {P : ℝ} (hP : P = 2 ∨ P = 3) : 12 * P ^ 7 < (P ^ 6 - 1) ^ 2 := by
  rcases hP with rfl | rfl <;> norm_num

/-- `C_q(2, 3) < 0` at `q = 2` and `q = 3`. -/
theorem localCov_two_three_neg_of_small (hp : p = 2 ∨ p = 3) : localCov p 2 3 < 0 := by
  have hP : (2 : ℝ) ≤ (p : ℝ) := two_le_cast_prime
  have hμ2 := inv_two_mul_sq_le_valuationMoment_two' (p := p)
  have hprod : 1 / (6 * (p : ℝ) ^ 5) ≤ valuationMoment p 2 * valuationMoment p 3 :=
    calc 1 / (6 * (p : ℝ) ^ 5) = 1 / (2 * (p : ℝ) ^ 2) * (1 / (3 * (p : ℝ) ^ 3)) := by
          field_simp
          ring
      _ ≤ valuationMoment p 2 * valuationMoment p 3 :=
          mul_le_mul hμ2 inv_three_mul_cube_le_valuationMoment_three' (by positivity)
            ((by positivity : (0 : ℝ) ≤ _).trans hμ2)
  have hnum : 2 / (p : ℝ) ^ 4 * ((p : ℝ) ^ 6 / ((p : ℝ) ^ 6 - 1) ^ 2) < 1 / (6 * (p : ℝ) ^ 5) := by
    refine mul_div_sq_lt_div (two_le_pow_of_two_le hP (by norm_num)) (by positivity) ?_
    calc 6 * (p : ℝ) ^ 5 * (2 / (p : ℝ) ^ 4 * (p : ℝ) ^ 6) = 12 * (p : ℝ) ^ 7 := by
          field_simp
          ring
      _ < ((p : ℝ) ^ 6 - 1) ^ 2 := twelve_mul_pow_seven_lt
          (hp.imp (fun h => by rw [h]; norm_num) fun h => by rw [h]; norm_num)
      _ = 1 * ((p : ℝ) ^ 6 - 1) ^ 2 := (one_mul _).symm
  rw [localCov_neg_iff]
  exact ((crossValuationMoment_two_three_le hp).trans_lt hnum).trans_le hprod

/-- For every prime `q`, `C_q(2, 3) < 0`. -/
@[bsd_tamagawa "T052"]
theorem localCov_two_three_neg_of_prime (q : ℕ) [Fact q.Prime] : localCov q 2 3 < 0 := by
  rcases prime_eq_two_or_eq_three_or_five_le (Fact.out : q.Prime) with h | h | h
  · exact localCov_two_three_neg_of_small (Or.inl h)
  · exact localCov_two_three_neg_of_small (Or.inr h)
  · exact localCov_neg_of_five_le h Nat.prime_two Nat.prime_three (by norm_num)

end WeierstrassCurve
