/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarAdditivity
public import BSDTamagawa.GOTTable.WildInStarOddAtTwo

/-!
# The tail of the odd `Iₘ*` family at `p = 2`

The residue cylinder

  `A`:  `a₄ ≡ 5 (mod 8)`,  `a₆ ≡ a₄ + 5 (mod 32)`

has mass `4 · 2⁻¹⁰ = 2⁻⁸`. On its nonsingular part Steps 1–5 of Tate's algorithm traverse and the
cubic of Step 6 has a double but not a triple root, so the answer is `Iₘ*` with `m ≠ 0` and
Tamagawa number `2` or `4`. The level `m = v₂(4a₄³ + 27a₆²) − 4` is unbounded on the cylinder and
is never computed. Since `a₄` is odd, no point of the cylinder is a dilate, so its two Tamagawa
halves lie in the minimal parts of the rows `t = 2` and `t = 4`, and together they carry the mass
of the cylinder.

The curve `4a₄³ + 27a₆² = 0` has the points `(a₄, a₆) = (−3w², 2w³)`, and for `w ≡ 1 (mod 4)` they
lie on the cylinder, `(−3, 2)` being the smallest; so no congruence decides nonsingularity here.
Each locus is intersected with `nonsingularLocus 2`, and the singular locus is null.

## Main definitions

* `WeierstrassCurve.AStarTailRes`, `WeierstrassCurve.aStarTailResidues`: the four classes
  `(5, 10)`, `(13, 18)`, `(21, 26)`, `(29, 2)` modulo `32`.
* `WeierstrassCurve.aStarTailLocus`: the cylinder.
* `WeierstrassCurve.aStarTailTwoLocus`, `WeierstrassCurve.aStarTailFourLocus`: its Tamagawa-`2` and
  Tamagawa-`4` halves.

## Main results

* `WeierstrassCurve.exists_step5_cubic_aStarTail`: on `a₄ = 5 + 8A`, `a₆ = 8A + 16E − 6`, Steps 1–5
  traverse and the cubic of Step 6 has a double but not a triple root.
* `WeierstrassCurve.run_eq_AStarTail_of_step5`: from that entry, Tate's algorithm answers `Iₘ*`
  with `m ≠ 0` and Tamagawa number `2` or `4`, at every prime.
* `WeierstrassCurve.exists_params_AStarTail`: the mod-`32` congruence parametrised.
* `WeierstrassCurve.volume_aStarTailLocus`: the cylinder has mass `1/256`.
-/

open CommRing Ideal CharP MeasureTheory Set

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### The entry: Steps 1–5 traverse and Step 6's cubic has a double but not a triple root

The class `a₄ ≡ 5 (mod 8)`, `a₆ ≡ −a₄ − 1 (mod 16)`, parametrised as `a₄ = 5 + 8A`,
`a₆ = 8A + 16E − 6`. The Step-2 shift `r` is odd and `t` is even, `a₄(V) = 4Q₄` and `a₆(V) = 4Q₆`,
and Step 6's cubic has residues `b ≡ 1 + ρ`, `c ≡ ρ`, `d ≡ 0` where `r = 1 + 2ρ`: `bc = 0 = d`
gives the double root and `b − c = 1` excludes a triple one. -/

open scoped Classical in
/-- **On `a₄ = 5 + 8A`, `a₆ = 8A + 16E − 6` over `ℤ_2`, Steps 1–5 of Tate's algorithm traverse and
the cubic of Step 6 has a double but not a triple root.** The parameter `E` is arbitrary. -/
theorem exists_step5_cubic_aStarTail (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2) {a₄ a₆ A E : ℤ_[p]}
    (ha₄ : a₄ = 5 + 8 * A) (ha₆ : a₆ = 8 * A + 16 * E - 6) :
    ∃ V : WeierstrassCurve ℤ_[p],
      Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok V ∧
        (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasDoubleRoot ∧
        ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasTripleRoot := by
  classical
  have hΔd : (p : ℤ_[p]) ∣ (ofShortNF a₄ a₆).Δ :=
    ⟨-8 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2), by rw [ofShortNF_Δ, hπ]; ring⟩
  obtain ⟨r, t, hV⟩ : ∃ r t : ℤ_[p], Step2.translate (p : ℤ_[p]) (ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆ := ⟨_, _, dite_eq_left hΔd⟩
  have hval2 := Step2.hasValuation_translate hΔd
  rw [hV] at hval2
  have hva₄ : (p : ℤ_[p]) ∣ a₄ + 3 * r ^ 2 := by
    have h := hval2.a₄
    rw [smul_ofShortNF_a₄, pow_one] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by linear_combination hc⟩
  have hva₆ : (p : ℤ_[p]) ∣ a₆ + r * a₄ + r ^ 3 - t ^ 2 := by
    have h := hval2.a₆
    rw [smul_ofShortNF_a₆, pow_one] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by linear_combination hc⟩
  obtain ⟨ρ, hr⟩ : ∃ ρ : ℤ_[p], r = 1 + 2 * ρ := by
    obtain ⟨y, hy | hy⟩ := exists_even_or_odd_two hp2 hπ r
    · exfalso
      obtain ⟨c, hc⟩ := hva₄
      rw [hy, hπ, ha₄] at hc
      exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_one
        ⟨c - 2 - 4 * A - 6 * y ^ 2, by rw [hπ]; linear_combination hc⟩)
    · exact ⟨y, hy⟩
  obtain ⟨mρ, hmρ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ ρ
  obtain ⟨τ, ht⟩ : ∃ τ : ℤ_[p], t = 2 * τ := by
    have h2 : (p : ℤ_[p]) ∣ a₆ + r * a₄ + r ^ 3 :=
      ⟨4 * mρ + 6 * ρ + 8 * E + 8 * A + 8 * ρ * mρ + 8 * A * ρ, by
        rw [hπ, ha₆, ha₄, hr]; linear_combination (4 + 8 * ρ) * hmρ⟩
    obtain ⟨c, hc⟩ := h2
    obtain ⟨d, hd⟩ := hva₆
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow (n := 2)
      (⟨c - d, by linear_combination hc - hd⟩ : (p : ℤ_[p]) ∣ t ^ 2)
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨mτ, hmτ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[p], x = 2 + 2 * A + 6 * mρ := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[p],
      x = 2 * mρ + 3 * ρ + 4 * E + 4 * A - τ ^ 2 + 4 * ρ * mρ + 4 * A * ρ := ⟨_, rfl⟩
  have hA4 : a₄ + 3 * r ^ 2 = 4 * Q₄ := by rw [ha₄, hr, hQ₄]; linear_combination 12 * hmρ
  have hA6 : a₆ + r * a₄ + r ^ 3 - t ^ 2 = 4 * Q₆ := by
    rw [ha₆, ha₄, hr, ht, hQ₆]; linear_combination (4 + 8 * ρ) * hmρ
  have h5run := step5_run_eq_ok_of_two hp2 hπ hΔd hV ht hA4 hA6
  have hVa₂ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₂ = 3 * r := by
    rw [smul_ofShortNF_a₂]; ring
  have hVa₆ : ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ 2 * Q₆ := by
    rw [smul_ofShortNF_a₆, hπ]; linear_combination hA6
  obtain ⟨s, hs⟩ : ∃ x : ℤ_[p],
      x = Step6.s (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨t₆, ht₆⟩ : ∃ x : ℤ_[p],
      x = Step6.t (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ_[p], s = 1 + 2 * σ := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ s - 3 * r := by
      rw [← mod_eq_zero, map_sub, hs, Step6.mod_s_two hp2, hVa₂, sub_self]
    rw [hπ, hr] at hk
    exact ⟨1 + 3 * ρ + k, by linear_combination hk⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ_[p], t₆ = Q₆ + 2 * j := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ t₆ - Q₆ := by
      rw [← mod_eq_zero, map_sub, ht₆, Step6.mod_t_two hp2,
        div_eq_of_eq_pow_mul_two hVa₆, sub_self]
    rw [hπ] at hk
    exact ⟨k, by linear_combination hk⟩
  obtain ⟨T₂, hT₂⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) * t₆ + t := ⟨_, rfl⟩
  have hW₆ : Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆ := by
    have h : Step6.translate (p : ℤ_[p]) ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 0 s ((p : ℤ_[p]) * t₆))
          • ((VariableChange.mk 1 r 0 t) • ofShortNF a₄ a₆) := by rw [hs, ht₆]
    rw [h]
    exact smul_smul_eq _ (by ring) (by ring) (by rw [hT₂]; ring)
  obtain ⟨X₂, hX₂⟩ : ∃ x : ℤ_[p], x = 1 + 3 * ρ - 2 * σ - 2 * σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨X₄, hX₄⟩ : ∃ x : ℤ_[p], x = Q₄ - s * (t₆ + τ) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ x : ℤ_[p], x = ρ + E + A + ρ * mρ + A * ρ := ⟨_, rfl⟩
  have hQ₆G : Q₆ = ρ ^ 2 - τ ^ 2 + 4 * G := by rw [hQ₆, hG]; linear_combination -hmρ
  have hK4 : (p : ℤ_[p]) ^ 2 ∣ Q₆ * (Q₆ + 2 * τ - 1) := by
    rw [pow_dvd_iff_toZModPow_eq_zero]
    have h4G : PadicInt.toZModPow 2 ((4 : ℤ_[p]) * G) = 0 :=
      (pow_dvd_iff_toZModPow_eq_zero 2 _).1 ⟨G, by rw [hπ]; ring⟩
    have hQr : PadicInt.toZModPow 2 Q₆
        = PadicInt.toZModPow 2 ρ ^ 2 - PadicInt.toZModPow 2 τ ^ 2 := by
      rw [hQ₆G, map_add, map_sub, map_pow, map_pow, h4G, add_zero]
    simp only [map_mul, map_sub, map_add, map_one, map_ofNat, hQr]
    exact zmod_double_root_two hp2 _ _
  obtain ⟨K, hK⟩ := hK4
  rw [hπ] at hK
  obtain ⟨X₆, hX₆⟩ : ∃ x : ℤ_[p], x = -2 * (K + j * (Q₆ + τ) + j ^ 2) := ⟨_, rfl⟩
  have hA6₂ : a₆ + r * a₄ + r ^ 3 = 4 * Q₆ + 4 * τ ^ 2 := by
    rw [ht] at hA6; linear_combination hA6
  have hW₆a₂ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂ = (p : ℤ_[p]) * X₂ := by
    rw [smul_ofShortNF_a₂, hπ, hr, hσ, hX₂]; ring
  have hW₆a₄ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄ = (p : ℤ_[p]) ^ 2 * X₄ := by
    rw [smul_ofShortNF_a₄, hX₄, hT₂, ht, hπ]; linear_combination hA4
  have hW₆a₆ : ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ 3 * X₆ := by
    rw [smul_ofShortNF_a₆, hX₆, hT₂, hj, ht, hπ]; linear_combination hA6₂ - 4 * hK
  have hX₄res : mod (p : ℤ_[p]) X₄ = mod (p : ℤ_[p]) ρ :=
    mod_eq_mod_of_dvd_sub_two ⟨1 - j + mτ - τ + 2 * mρ - 2 * ρ - 2 * E - A - 2 * σ * j
      + 2 * mτ * σ - 2 * τ * σ - 2 * mρ * σ - 3 * ρ * σ - 2 * ρ * mρ - 4 * E * σ - 4 * A * σ
      - 2 * A * ρ - 4 * ρ * mρ * σ - 4 * A * ρ * σ, by
      rw [hX₄, hQ₄, hj, hQ₆, hσ, hπ]; linear_combination (1 + 2 * σ) * hmτ⟩
  have hcubb : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).b
      = mod (p : ℤ_[p]) (1 + ρ) := by
    change mod (p : ℤ_[p])
      (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₂) (p : ℤ_[p])) = _
    rw [div_eq_of_eq_mul_two hW₆a₂]
    exact mod_eq_mod_of_dvd_sub_two ⟨ρ - σ - σ ^ 2, by rw [hX₂, hπ]; ring⟩
  have hcubc : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c
      = mod (p : ℤ_[p]) ρ := by
    change mod (p : ℤ_[p])
      (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄) ((p : ℤ_[p]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two hW₆a₄]
    exact hX₄res
  have hcubd : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d = 0 := by
    change mod (p : ℤ_[p])
      (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆) ((p : ℤ_[p]) ^ 3)) = _
    rw [div_eq_of_eq_pow_mul_two hW₆a₆, mod_eq_zero]
    exact ⟨-(K + j * (Q₆ + τ) + j ^ 2), by rw [hX₆, hπ]; ring⟩
  have hdbl : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      1 1).HasDoubleRoot := by
    refine hasDoubleRoot_of_mul_eq_two hp2 rfl ?_
    rw [hcubb, hcubc, hcubd, ← map_mul, mod_eq_zero]
    exact ⟨mρ, by rw [hπ]; linear_combination hmρ⟩
  have hntr : ¬ (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      1 1).HasTripleRoot := by
    refine not_hasTripleRoot_of_sub_eq_one_two hp2 ?_
    rw [hcubb, hcubc, ← map_sub, show (1 : ℤ_[p]) + ρ - ρ = 1 from by ring, map_one]
  exact ⟨_, h5run, hW₆ ▸ hdbl, hW₆ ▸ hntr⟩

/-! ### The answer is `Iₘ*` with `m ≠ 0`, of Tamagawa number `2` or `4` -/

open scoped Classical in
/-- **Steps 1–5 succeed and Step 6's cubic has a double but not a triple root: the answer is `Iₘ*`
with `m ≠ 0` and Tamagawa number `2` or `4`.** -/
theorem run_eq_AStarTail_of_step5 {W V : WeierstrassCurve ℤ_[p]} (hΔ : W.Δ ≠ 0)
    (h5 : Step5.run (p : ℤ_[p]) W = Except.ok V)
    (hdbl : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasDoubleRoot)
    (hntr : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasTripleRoot) :
    (∃ m, m ≠ 0 ∧ (TateAlgorithm.run (W := W)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! m) ∧
      ((TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 ∨
        (TateAlgorithm.run (W := W) PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 4) := by
  classical
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h6 : Step6.run (p : ℤ_[p]) W = Except.ok (Step6.translate (p : ℤ_[p]) V) := by
    rw [Step6.run.eq_def, h5]
    simp only [except_ok_bind]
    exact ite_eq_left hdbl
  obtain ⟨out, h7, m, hm, hκ⟩ := Step7.run_eq_error_of_not_hasTripleRoot hΔ h6 hntr
  rw [run_eq_of_step11_error hϖ hΔ (step11_error_of_step7 hΔ h7)]
  exact ⟨⟨m, hm, hκ⟩, Step7.run_error_tamagawaNumber_eq_two_or_four hΔ h6 hntr h7⟩

/-! ### The four residue classes modulo `32` -/

/-- **The residue condition cutting out the tail**: `a₄ ≡ 5 (mod 8)` and `a₆ ≡ a₄ + 5 (mod 32)`,
which modulo `32` is these four classes. -/
abbrev AStarTailRes (a e : ZMod (2 ^ 5)) : Prop :=
  (a = 5 ∧ e = 10) ∨ (a = 13 ∧ e = 18) ∨ (a = 21 ∧ e = 26) ∨ (a = 29 ∧ e = 2)

/-- The four residue pairs of `AStarTailRes`, as a `Finset`. -/
def aStarTailResidues : Finset (ZMod (2 ^ 5) × ZMod (2 ^ 5)) :=
  {(5, 10), (13, 18), (21, 26), (29, 2)}

/-- The set `aStarTailResidues` has exactly four elements. -/
theorem card_aStarTailResidues : aStarTailResidues.card = 4 := by decide

/-- A residue pair lies in `aStarTailResidues` if and only if it satisfies `AStarTailRes`. -/
theorem mem_aStarTailResidues_iff {c : ZMod (2 ^ 5) × ZMod (2 ^ 5)} :
    c ∈ aStarTailResidues ↔ AStarTailRes c.1 c.2 := by
  simp [aStarTailResidues, Prod.ext_iff]

set_option maxRecDepth 20000 in
/-- **The two congruences the parametrisation needs**, by exhaustion over `(ZMod 32)²`: each class
has `a₄ ≡ 5 (mod 8)` and `a₆ − a₄ − 5 ≡ 0 (mod 32)`. -/
theorem aStarTailRes_congr : ∀ a e : ZMod (2 ^ 5), AStarTailRes a e →
    (ZMod.cast (a - 5) : ZMod (2 ^ 3)) = 0 ∧ e - a - 5 = 0 := by decide

set_option maxRecDepth 20000 in
/-- On the residue set `a₄` is odd, so `16 ∤ a₄` and no point of the locus is a dilate. -/
theorem aStarTailRes_notDvd : ∀ a e : ZMod (2 ^ 5), AStarTailRes a e →
    (ZMod.cast a : ZMod (2 ^ 4)) ≠ 0 := by decide

/-! ### From a residue class modulo `32` to the parameters -/

/-- **The tail's congruence, parametrised.** `a₄ ≡ 5 (mod 8)` gives `a₄ = 5 + 8A`, and
`a₆ ≡ a₄ + 5 (mod 32)` then gives `a₆ = 8A + 10 + 32G = 8A + 16(1 + 2G) − 6`. -/
theorem exists_params_AStarTail {a₄ a₆ : ℤ_[2]}
    (h1 : (ZMod.cast (PadicInt.toZModPow 5 a₄ - 5) : ZMod (2 ^ 3)) = 0)
    (h2 : PadicInt.toZModPow 5 a₆ - PadicInt.toZModPow 5 a₄ - 5 = 0) :
    ∃ A E : ℤ_[2], a₄ = 5 + 8 * A ∧ a₆ = 8 * A + 16 * E - 6 := by
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  obtain ⟨A, hA⟩ : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ a₄ - 5 := by
    refine pow_dvd_of_cast_toZModPow_eq_zero (n := 5) (by norm_num) ?_
    rwa [map_sub, map_ofNat]
  obtain ⟨G, hG⟩ : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ a₆ - a₄ - 5 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero]
    rwa [map_sub, map_sub, map_ofNat]
  rw [hcast] at hA hG
  exact ⟨A, 1 + 2 * G, by linear_combination hA, by linear_combination hG + hA⟩

/-! ### The locus, its mass, and its two Tamagawa halves -/

/-- The **tail locus** of the odd `Iₘ*` family at `2`: four residue classes modulo `32`. -/
noncomputable def aStarTailLocus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 5 ⁻¹' (aStarTailResidues : Set (ZMod (2 ^ 5) × ZMod (2 ^ 5)))

/-- A point `(a₄, a₆)` lies in the tail locus if and only if its reduction modulo `32` satisfies
`AStarTailRes`. -/
theorem mem_aStarTailLocus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ aStarTailLocus ↔
      AStarTailRes (PadicInt.toZModPow 5 x.1) (PadicInt.toZModPow 5 x.2) := by
  rw [aStarTailLocus, mem_preimage, Finset.mem_coe, mem_aStarTailResidues_iff,
    PadicInt.redPairPow]

/-- The tail locus `aStarTailLocus` is measurable. -/
theorem measurableSet_aStarTailLocus : MeasurableSet aStarTailLocus :=
  PadicInt.measurableSet_preimage_redPairPow 5 aStarTailResidues

/-- `4 · 2⁻¹⁰ = 1/256`. -/
theorem four_mul_inv_pow_ten_eq_aStarTail :
    ((4 : ℕ) : ℝ≥0∞) * (((2 : ℕ) : ℝ≥0∞)⁻¹) ^ (2 * 5) = 1 / 256 := by
  rw [← ENNReal.inv_pow, show (((2 : ℕ) : ℝ≥0∞)) ^ (2 * 5) = 1024 by norm_num,
    ← div_eq_mul_inv, show ((4 : ℕ) : ℝ≥0∞) = 4 by norm_num]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The mass of the tail locus is `4/1024 = 1/256`.** -/
theorem volume_aStarTailLocus :
    (volume : Measure (ℤ_[2] × ℤ_[2])) aStarTailLocus = 1 / 256 := by
  rw [aStarTailLocus, PadicInt.volume_preimage_redPairPow, card_aStarTailResidues,
    four_mul_inv_pow_ten_eq_aStarTail]

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- The `c = 2` half of the tail locus. -/
noncomputable def aStarTailTwoLocus : Set (ℤ_[2] × ℤ_[2]) :=
  aStarTailLocus ∩ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- The `c = 4` half of the tail locus. -/
noncomputable def aStarTailFourLocus : Set (ℤ_[2] × ℤ_[2]) :=
  aStarTailLocus ∩ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4)

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- The `c = 2` half `aStarTailTwoLocus` of the tail locus is measurable. -/
theorem measurableSet_aStarTailTwoLocus : MeasurableSet aStarTailTwoLocus :=
  measurableSet_aStarTailLocus.inter
    (MeasurableSet.iUnion fun κ => (isOpen_stratFibre (p := 2) (κ, 2)).measurableSet)

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- The `c = 4` half `aStarTailFourLocus` of the tail locus is measurable. -/
theorem measurableSet_aStarTailFourLocus : MeasurableSet aStarTailFourLocus :=
  measurableSet_aStarTailLocus.inter
    (MeasurableSet.iUnion fun κ => (isOpen_stratFibre (p := 2) (κ, 4)).measurableSet)

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The two halves are disjoint.** -/
theorem disjoint_aStarTailTwoLocus_aStarTailFourLocus :
    Disjoint aStarTailTwoLocus aStarTailFourLocus := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨-, h2⟩ := hx
  obtain ⟨-, h4⟩ := hx'
  obtain ⟨κ, hκ⟩ := Set.mem_iUnion.1 h2
  obtain ⟨κ', hκ'⟩ := Set.mem_iUnion.1 h4
  exact (Set.disjoint_left.1 (disjoint_stratFibre_of_ne_snd (κ := κ) (κ' := κ')
    (by norm_num : (2 : ℕ) ≠ 4)) hκ) hκ'

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- **The two halves cover the nonsingular part of the tail locus.** -/
theorem aStarTailLocus_inter_nonsingularLocus_subset_union :
    aStarTailLocus ∩ nonsingularLocus 2 ⊆ aStarTailTwoLocus ∪ aStarTailFourLocus := by
  intro x ⟨hx, hUp⟩
  obtain ⟨h1, h2⟩ := aStarTailRes_congr _ _ (mem_aStarTailLocus_iff.1 hx)
  obtain ⟨A, E, ha₄, ha₆⟩ := exists_params_AStarTail h1 h2
  obtain ⟨V, h5, hdbl, hntr⟩ := exists_step5_cubic_aStarTail (p := 2) rfl (by norm_num) ha₄ ha₆
  obtain ⟨⟨m, hm, hκ⟩, hc⟩ := run_eq_AStarTail_of_step5 hUp h5 hdbl hntr
  rcases hc with hc | hc
  · exact Or.inl ⟨hx, Set.mem_iUnion.2 ⟨KodairaSymbol.I! m,
      (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)⟩⟩
  · exact Or.inr ⟨hx, Set.mem_iUnion.2 ⟨KodairaSymbol.I! m,
      (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)⟩⟩

/-! ### Minimality, and membership of the two rows -/

/-- **No point of the tail locus is a dilate**: on it `a₄` is odd. -/
theorem notMem_range_of_mem_aStarTailLocus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ aStarTailLocus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  refine aStarTailRes_notDvd _ _ (mem_aStarTailLocus_iff.1 hx) ?_
  rw [PadicInt.cast_toZModPow 4 5 (by norm_num), ← PadicInt.pow_dvd_iff_toZModPow_eq_zero]
  exact hdvd

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- The `c = 2` half lies in the minimal part of the `t = 2` row. -/
theorem aStarTailTwoLocus_subset_headMinimal :
    aStarTailTwoLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 2)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx => ⟨hx.2, notMem_range_of_mem_aStarTailLocus hx.1⟩

open BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction TateAlgorithm in
/-- The `c = 4` half lies in the minimal part of the `t = 4` row. -/
theorem aStarTailFourLocus_subset_headMinimal :
    aStarTailFourLocus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 4)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx => ⟨hx.2, notMem_range_of_mem_aStarTailLocus hx.1⟩

/-! ### The mass of the two halves together

The singular locus is null, so the two halves carry the cylinder's whole mass `2⁻⁸` between
them. -/

open BSDTamagawa.LocalConstancy in
/-- **The two halves' masses sum to at least the cylinder's.** -/
theorem le_volume_aStarTailTwoLocus_add_volume_aStarTailFourLocus :
    (1 : ℝ≥0∞) / 256 ≤ (volume : Measure (ℤ_[2] × ℤ_[2])) aStarTailTwoLocus
      + volume aStarTailFourLocus := by
  have hcover : (volume : Measure (ℤ_[2] × ℤ_[2])) aStarTailLocus
      ≤ volume (aStarTailTwoLocus ∪ aStarTailFourLocus) := by
    refine le_trans (le_of_eq ?_) (measure_mono aStarTailLocus_inter_nonsingularLocus_subset_union)
    refine le_antisymm ?_ (measure_mono Set.inter_subset_left)
    refine le_trans (measure_mono (show aStarTailLocus
        ⊆ (aStarTailLocus ∩ nonsingularLocus 2) ∪ (nonsingularLocus 2)ᶜ from fun y hy => by
      by_cases h : y ∈ nonsingularLocus 2
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr h)) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [volume_compl_nonsingularLocus, add_zero]
  rw [← volume_aStarTailLocus]
  refine le_trans hcover (le_of_eq ?_)
  exact measure_union disjoint_aStarTailTwoLocus_aStarTailFourLocus
    measurableSet_aStarTailFourLocus

end WeierstrassCurve

end
