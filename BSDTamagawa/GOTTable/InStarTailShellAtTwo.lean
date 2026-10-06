/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.InStarFlipRunAtTwo
public import BSDTamagawa.GOTTable.WildInStarEvenTailAtTwo
public import BSDTamagawa.GOTTable.WildInStarOddTailAtTwo

/-!
# The level shells of the `Iₘ*` tail cylinders at `p = 2`, and the equality of their two halves

Two residue cylinders of the coefficient plane at `2` are considered: the deep cylinder
`a₄ ≡ 20`, `a₆ ≡ 16 (mod 32)` and the odd tail `a₄ ≡ 5 (mod 8)`, `a₆ ≡ a₄ + 5 (mod 32)`. On each,
every nonsingular point has Kodaira symbol `Iₘ*` with Tamagawa number `2` or `4`, and the two
Tamagawa halves have equal mass.

Each cylinder is cut into the shells `bStarTailShell m c = bStarTailLocus ∩ stratFibre 2 (Iₘ*, c)`
(respectively `aStarTailShell m c`). On the cylinders the reported index satisfies `m ≥ 2`, since
the entry model's `a₃` is divisible by `8`, so the level-`2` `Y`-quadratic has a double root. The
shift `(a₄, a₆) ↦ (a₄, a₆ + 2^(m+3))` is measure-preserving, preserves the cylinder because
`32 ∣ 2^(m+3)`, and, by the flip at `TateAlgorithm.run`, keeps the symbol `Iₘ*` while exchanging
Tamagawa `2` and `4`. As the flip is a biconditional, the same shift maps the `c = 2` part of a
shell into the `c = 4` part and conversely, off the null set where the image is singular. Summing
over the shells gives equality of the two halves; on the odd tail each half therefore has mass
`1/512`.

## Main definitions

* `WeierstrassCurve.TailShell.shift`: the map `(a₄, a₆) ↦ (a₄, a₆ + 2^v)`.
* `WeierstrassCurve.bStarTailShell`, `WeierstrassCurve.aStarTailShell`: the shells of level `m`
  and Tamagawa number `c` of the two cylinders.

## Main results

* `WeierstrassCurve.TailShell.volume_preimage_shift`: the shift is measure-preserving.
* `WeierstrassCurve.TailShell.toZModPow_shift`: an offset `2^v` with `5 ≤ v` leaves both residues
  modulo `32` unchanged.
* `WeierstrassCurve.TailShell.exists_two_le_kodairaSymbol_of_hasDoubleRoot`: once the level-`2`
  `Y`-quadratic has a double root, the reported index is at least `2`.
* `WeierstrassCurve.TailShell.bstar_exists_two_le_kodairaSymbol`,
  `WeierstrassCurve.TailShell.astar_exists_two_le_kodairaSymbol`: on the cylinders, `Iₘ*` with
  `m ≥ 2`.
* `WeierstrassCurve.exists_step7_entry_aStarTail`: the Step-7 entry model on the odd tail.
* `WeierstrassCurve.TailShell.bstar_volume_shell_eq`,
  `WeierstrassCurve.TailShell.astar_volume_shell_eq`: the two halves of a shell of level `m ≥ 2`
  have equal mass.
* `WeierstrassCurve.TailShell.bstarTailFlip`, `WeierstrassCurve.TailShell.astarTailFlip`: the two
  Tamagawa halves of each cylinder have equal mass.
* `WeierstrassCurve.TailShell.astar_volume_eq`: each half of the odd tail has mass `1/512`.
-/

open CommRing Ideal MeasureTheory Set

open scoped ENNReal

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm BSDTamagawa.LocalConstancy BSDTamagawa.LocalReduction

/-! ### The shift, and the two facts about it that are not about Tate's algorithm -/

/-- **The level-`v` shift**: add `2^v` to `a₆` and leave `a₄` unchanged. -/
noncomputable def TailShell.shift (v : ℕ) : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2] :=
  fun x => (x.1, x.2 + ((2 : ℕ) : ℤ_[2]) ^ v)

/-- **The shift preserves the volume of every set**, being the translation by `(0, 2^v)` for the
left-invariant product volume on `ℤ_[2] × ℤ_[2]`. -/
theorem TailShell.volume_preimage_shift (v : ℕ) (S : Set (ℤ_[2] × ℤ_[2])) :
    (volume : Measure (ℤ_[2] × ℤ_[2])) (TailShell.shift v ⁻¹' S) = volume S := by
  have hinv : (volume : Measure (ℤ_[2] × ℤ_[2])).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  have h : TailShell.shift v
      = fun x : ℤ_[2] × ℤ_[2] => ((0, ((2 : ℕ) : ℤ_[2]) ^ v) : ℤ_[2] × ℤ_[2]) + x := by
    funext x
    exact Prod.ext (by simp [TailShell.shift]) (by simp [TailShell.shift, add_comm])
  rw [h, measure_preimage_add]

/-- **The set where the shifted point is singular is null.** The shift is measure-preserving and
the singular locus is null. -/
theorem TailShell.volume_preimage_compl_nonsingularLocus (v : ℕ) :
    (volume : Measure (ℤ_[2] × ℤ_[2])) (TailShell.shift v ⁻¹' (nonsingularLocus 2)ᶜ) = 0 := by
  rw [TailShell.volume_preimage_shift, volume_compl_nonsingularLocus]

/-- **An offset `2^v` with `5 ≤ v` is invisible modulo `32`**: both residues modulo `32` are
unchanged by the shift. -/
theorem TailShell.toZModPow_shift {v : ℕ} (hv : 5 ≤ v) (x : ℤ_[2] × ℤ_[2]) :
    PadicInt.toZModPow 5 (TailShell.shift v x).1 = PadicInt.toZModPow 5 x.1 ∧
      PadicInt.toZModPow 5 (TailShell.shift v x).2 = PadicInt.toZModPow 5 x.2 := by
  refine ⟨rfl, ?_⟩
  have h : ((2 : ℕ) : ℤ_[2]) ^ 5 ∣ ((2 : ℕ) : ℤ_[2]) ^ v := pow_dvd_pow _ hv
  rw [TailShell.shift, map_add, PadicInt.pow_dvd_iff_toZModPow_eq_zero.1 h, add_zero]

/-! ### The reported index is at least `2` once the level-`2` `Y`-quadratic has a double root

At the entry level the general bound only gives `m ≥ 1`, and `I₁*` is the odd exit at level `2`.
If the level-`2` `X`-cubic also has a double root the loop recurses to level `3`, where the bound
reads `m ≥ 2`; otherwise the even exit reports `I₂*`. -/

variable {p : ℕ} [Fact p.Prime]

open scoped Classical in
/-- **A double root of the level-`2` `Y`-quadratic forces `2 ≤ m`.** -/
theorem TailShell.exists_two_le_kodairaSymbol_of_hasDoubleRoot {W V : WeierstrassCurve ℤ_[p]}
    (hΔ : W.Δ ≠ 0) (h5 : Step5.run (p : ℤ_[p]) W = Except.ok V)
    (hdbl : (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasDoubleRoot)
    (hntr : ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasTripleRoot)
    (hY : (quadratic (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2).HasDoubleRoot) :
    ∃ m, 2 ≤ m ∧ (TateAlgorithm.run (W := W)
      PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! m := by
  classical
  have hϖ : (p : ℤ_[p]) ≠ 0 := PadicInt.uniformizer_ne_zero
  have h6 : Step6.run (p : ℤ_[p]) W = Except.ok (Step6.translate (p : ℤ_[p]) V) := by
    rw [Step6.run.eq_def, h5]
    simp only [except_ok_bind]
    exact ite_eq_left hdbl
  have hval6 := Step6.run_hasValuation hϖ h6
  have hΔc : (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)).Δ ≠ 0 := by
    rw [Step7.translate_Δ, Step6.run_Δ h6]; exact hΔ
  have hvc := Step7.hasValuation_translate hϖ hval6 hdbl hntr
  have ha₂c := Step7.not_dvd_translate_a₂ hϖ hval6.a₂ hdbl hntr
  rw [run_eq_of_step11_error hϖ hΔ (step11_error_of_step7 hΔ
    (Step7.run_eq_of_step6_ok_of_not_hasTripleRoot hϖ hΔ h6 hntr hΔc hvc ha₂c))]
  by_cases hX : (cubic (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p])
      (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2) 0 2).HasDoubleRoot
  · have hΔ' : (Step7.translateX (p : ℤ_[p]) (Step7.translateY (p : ℤ_[p])
        (Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)) 2) 2).Δ ≠ 0 := by
      rw [Step7.translateX_Δ, Step7.translateY_Δ]; exact hΔc
    have hvY := Step7.hasValuation_translateY (n := 2) le_rfl hϖ hvc hY
    have ha₂Y := Step7.not_dvd_translateY_a₂ 2 ha₂c
    have hW' := Step7.hasValuation_translateX (n := 2) le_rfl hϖ hvY ha₂Y hX
    have ha₂' := Step7.not_dvd_translateX_a₂ (n := 2) le_rfl hϖ hvY.a₂ ha₂Y
    rw [Step7.subprocedure_eq_subprocedure hϖ hΔc le_rfl hvc ha₂c hY hX hΔ'
      (by norm_num : 2 ≤ 2 + 1) hW' ha₂']
    obtain ⟨m, hm, hle⟩ := Step7.subprocedure_exists_kodairaSymbol_two_mul_le hϖ hΔ'
      (by norm_num : 2 ≤ 2 + 1) hW' ha₂'
    exact ⟨m, by omega, hm⟩
  · rw [Step7.subprocedure_eq_of_not_hasDoubleRoot_cubic hϖ hΔc le_rfl hvc ha₂c hY hX]
    exact ⟨2 * 2 - 2, by norm_num, rfl⟩

/-- **The level-`2` `Y`-quadratic of an entry model `⟨1, R, S, 4μ⟩ · (a₄, a₆)` has a double root.**
Its `a₃` is `2 · 4μ = 8μ`, so the linear coefficient `a₃/ϖ² = 2μ` reduces to `0`. -/
theorem TailShell.hasDoubleRoot_quadratic_entry_even (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2)
    (a₄ a₆ R S μ : ℤ_[p]) :
    (quadratic (p : ℤ_[p])
      ((VariableChange.mk 1 R S (4 * μ)) • ofShortNF a₄ a₆) 2).HasDoubleRoot := by
  have ha₃ : ((VariableChange.mk 1 R S (4 * μ)) • ofShortNF a₄ a₆).a₃
      = (p : ℤ_[p]) ^ 2 * (2 * μ) := by
    rw [smul_ofShortNF_a₃, hπ]; ring
  refine hasDoubleRoot_quadratic_zero_two hp2 rfl rfl ?_
  rw [quadratic, div_eq_of_eq_pow_mul_two ha₃, mod_eq_zero]
  exact ⟨μ, by rw [hπ]⟩

open scoped Classical in
/-- **On the deep cylinder the reported index is at least `2`.** -/
theorem TailShell.bstar_exists_two_le_kodairaSymbol {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ bStarTailLocus) (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) :
    ∃ m, 2 ≤ m ∧ (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! m := by
  classical
  obtain ⟨A, F, ha₄, ha₆⟩ := bstarTail_exists_params hx
  obtain ⟨V, ν, σ, μ, h5, hdbl, hntr, hW₇⟩ :=
    exists_step7_entry_even_two (p := 2) (a₄ := x.1) (a₆ := x.2) (A₀ := 2 + 4 * A)
      (B := 1 + 2 * F) rfl (by norm_num) ha₄ ha₆
  refine TailShell.exists_two_le_kodairaSymbol_of_hasDoubleRoot hΔ h5 hdbl hntr ?_
  rw [hW₇]
  exact TailShell.hasDoubleRoot_quadratic_entry_even (p := 2) rfl (by norm_num) _ _ _ _ μ

/-! ### The odd tail cylinder -/

open scoped Classical in
/-- **The Step-7 entry model on the odd tail `a₄ = 5 + 8A`, `a₆ = 8A + 16E − 6`.** Steps 1–5
traverse, Step 6's cubic has a double but not a triple root, and the model on which Step 7 enters
its loop is `⟨1, R, S, 4μ⟩ · (a₄, a₆)`, whose `T`-coefficient is divisible by `4`. -/
theorem exists_step7_entry_aStarTail (hp2 : p = 2) (hπ : (p : ℤ_[p]) = 2) {a₄ a₆ A E : ℤ_[p]}
    (ha₄ : a₄ = 5 + 8 * A) (ha₆ : a₆ = 8 * A + 16 * E - 6) :
    ∃ V : WeierstrassCurve ℤ_[p], ∃ R S μ : ℤ_[p],
      Step5.run (p : ℤ_[p]) (ofShortNF a₄ a₆) = Except.ok V ∧
        (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasDoubleRoot ∧
        ¬ (cubic (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V) 1 1).HasTripleRoot ∧
        Step7.translate (p : ℤ_[p]) (Step6.translate (p : ℤ_[p]) V)
          = (VariableChange.mk 1 R S (4 * μ)) • ofShortNF a₄ a₆ := by
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
  obtain ⟨r₇, hr₇⟩ : ∃ x : ℤ_[p],
      x = Step7.r (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := ⟨_, rfl⟩
  obtain ⟨k₇, hk₇⟩ : ∃ k : ℤ_[p], r₇ = ρ + 2 * k := by
    obtain ⟨k, hk⟩ : (p : ℤ_[p]) ∣ r₇ - ρ := by
      rw [← mod_eq_zero, map_sub, hr₇, Step7.mod_r_two hp2,
        div_eq_of_eq_pow_mul_two hW₆a₄, hX₄res, sub_self]
    rw [hπ] at hk
    exact ⟨k, by linear_combination hk⟩
  obtain ⟨R₇, hR₇⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) * r₇ + r := ⟨_, rfl⟩
  obtain ⟨T₇, hT₇⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) * r₇ * s + T₂ := ⟨_, rfl⟩
  have hW₇ : Step7.translate (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
      = (VariableChange.mk 1 R₇ s T₇) • ofShortNF a₄ a₆ := by
    have h : Step7.translate (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆)
        = (VariableChange.mk 1 ((p : ℤ_[p]) * r₇) 0 0)
          • ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) := by rw [hr₇]
    rw [h]
    exact smul_smul_eq _ (by rw [hR₇]) (by ring) (by rw [hT₇]; ring)
  obtain ⟨τ₈, hτ₈⟩ : ∃ x : ℤ_[p], x = k₇ + j - mτ + τ + mρ + 2 * ρ + 2 * E + 2 * A
    + 2 * σ * k₇ + ρ * σ + 2 * ρ * mρ + 2 * A * ρ := ⟨_, rfl⟩
  have hT₇v : T₇ = 4 * τ₈ := by
    rw [hT₇, hT₂, hπ, ht, hk₇, hσ, hj, hQ₆, hτ₈]; linear_combination -2 * hmτ
  exact ⟨_, R₇, s, τ₈, h5run, hW₆ ▸ hdbl, hW₆ ▸ hntr, by rw [hW₆, hW₇, hT₇v]⟩

/-! ### The shells of the deep cylinder -/

/-- **The shell of level `m` and Tamagawa number `c`** of the deep cylinder: its points whose
reduction datum is exactly `(Iₘ*, c)`. -/
noncomputable def bStarTailShell (m c : ℕ) : Set (ℤ_[2] × ℤ_[2]) :=
  bStarTailLocus ∩ stratFibre 2 (KodairaSymbol.I! m, c)

/-- The shell `bStarTailShell m c` is measurable. -/
theorem measurableSet_bStarTailShell (m c : ℕ) : MeasurableSet (bStarTailShell m c) :=
  measurableSet_bStarTailLocus.inter (isOpen_stratFibre (p := 2) _).measurableSet

/-- A point of a shell is nonsingular. -/
theorem TailShell.bstar_shell_mem_nonsingularLocus {m c : ℕ} {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ bStarTailShell m c) : x ∈ nonsingularLocus 2 := stratFibre_subset _ hx.2

/-- The reduction datum of a point of the shell of level `m`, read off. -/
theorem TailShell.bstar_shell_strat {m c : ℕ} {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ bStarTailShell m c) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero (TailShell.bstar_shell_mem_nonsingularLocus hx)).kodairaSymbol
          = KodairaSymbol.I! m ∧
      (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero
          (TailShell.bstar_shell_mem_nonsingularLocus hx)).tamagawaNumber = c := by
  have h := (mem_stratFibre_iff (TailShell.bstar_shell_mem_nonsingularLocus hx)).1 hx.2
  rw [strat] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Membership of a shell, from the reduction datum. -/
theorem TailShell.bstar_mem_shell {m c : ℕ} {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ bStarTailLocus)
    (hUp : x ∈ nonsingularLocus 2)
    (hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = KodairaSymbol.I! m)
    (hc : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hUp).tamagawaNumber = c) :
    x ∈ bStarTailShell m c :=
  ⟨hx, (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)⟩

/-- **The `c = 2` half is exactly the union of its shells.** -/
theorem TailShell.bstar_iUnion_shell_two :
    bStarTailTwoLocus = ⋃ m, bStarTailShell m 2 := by
  refine Set.eq_of_subset_of_subset (fun x hx => ?_) (Set.iUnion_subset fun m y hy => ?_)
  · obtain ⟨hxc, hst⟩ := hx
    obtain ⟨κ, hκ⟩ := Set.mem_iUnion.1 hst
    have hUp : x ∈ nonsingularLocus 2 := stratFibre_subset _ hκ
    obtain ⟨⟨m, -, hm⟩, -⟩ := bstarTail_exists_kodairaSymbol_and_tamagawaNumber hxc hUp
    have h := (mem_stratFibre_iff hUp).1 hκ
    rw [strat] at h
    exact Set.mem_iUnion.2 ⟨m, TailShell.bstar_mem_shell hxc hUp hm (congrArg Prod.snd h)⟩
  · exact ⟨hy.1, Set.mem_iUnion.2 ⟨KodairaSymbol.I! m, hy.2⟩⟩

/-- **The `c = 4` half is exactly the union of its shells**, by the same reading. -/
theorem TailShell.bstar_iUnion_shell_four :
    bStarTailFourLocus = ⋃ m, bStarTailShell m 4 := by
  refine Set.eq_of_subset_of_subset (fun x hx => ?_) (Set.iUnion_subset fun m y hy => ?_)
  · obtain ⟨hxc, hst⟩ := hx
    obtain ⟨κ, hκ⟩ := Set.mem_iUnion.1 hst
    have hUp : x ∈ nonsingularLocus 2 := stratFibre_subset _ hκ
    obtain ⟨⟨m, -, hm⟩, -⟩ := bstarTail_exists_kodairaSymbol_and_tamagawaNumber hxc hUp
    have h := (mem_stratFibre_iff hUp).1 hκ
    rw [strat] at h
    exact Set.mem_iUnion.2 ⟨m, TailShell.bstar_mem_shell hxc hUp hm (congrArg Prod.snd h)⟩
  · exact ⟨hy.1, Set.mem_iUnion.2 ⟨KodairaSymbol.I! m, hy.2⟩⟩

/-- **Shells at distinct levels are disjoint**, the strata over distinct Kodaira symbols being
disjoint. -/
theorem TailShell.bstar_pairwise_disjoint_shell (c : ℕ) :
    Pairwise (Function.onFun Disjoint fun m => bStarTailShell m c) := by
  intro m m' hmm
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  exact (Set.disjoint_left.1 (disjoint_stratFibre_of_ne (p := 2)
    (κ := KodairaSymbol.I! m) (κ' := KodairaSymbol.I! m')
    (fun h => hmm (KodairaSymbol.I!.inj h)) c c) hx.2) hx'.2

/-! ### The flip on one shell -/

open scoped Classical in
/-- **The flip on the deep cylinder.** For a point of the cylinder with reported symbol `Iₘ*`,
adding `2^(m+3)` to `a₆` keeps the symbol and exchanges Tamagawa `4` with `2`. -/
theorem TailShell.bstar_run_flip {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ bStarTailLocus) {m : ℕ}
    (hUp : x ∈ nonsingularLocus 2)
    (hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = KodairaSymbol.I! m)
    (hΔ' : (ofShortNF x.1 (x.2 + ((2 : ℕ) : ℤ_[2]) ^ (m + 3))).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF x.1 (x.2 + ((2 : ℕ) : ℤ_[2]) ^ (m + 3)))
        PadicInt.uniformizer_ne_zero hΔ').kodairaSymbol = KodairaSymbol.I! m ∧
      ((TateAlgorithm.run (W := ofShortNF x.1 (x.2 + ((2 : ℕ) : ℤ_[2]) ^ (m + 3)))
          PadicInt.uniformizer_ne_zero hΔ').tamagawaNumber = 4 ↔
        (TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hUp).tamagawaNumber = 2) := by
  classical
  obtain ⟨A, F, ha₄, ha₆⟩ := bstarTail_exists_params hx
  obtain ⟨V, ν, σ, μ, h5, hdbl, hntr, -⟩ :=
    exists_step7_entry_even_two (p := 2) (a₄ := x.1) (a₆ := x.2) (A₀ := 2 + 4 * A)
      (B := 1 + 2 * F) rfl (by norm_num) ha₄ ha₆
  exact FlipRun.run_flip_ofShortNF (p := 2) rfl hUp hΔ' h5 hdbl hntr hκ rfl

/-- **The shift by `2^(m+3)` sends the `c = 2` part of a shell of level `m ≥ 2` into its `c = 4`
part**, off the null set where the image is singular. -/
theorem TailShell.bstar_shell_two_subset {m : ℕ} (hm : 2 ≤ m) :
    bStarTailShell m 2 ∩ TailShell.shift (m + 3) ⁻¹' nonsingularLocus 2
      ⊆ TailShell.shift (m + 3) ⁻¹' bStarTailShell m 4 := by
  intro x ⟨hx, hUp'⟩
  obtain ⟨hκ, hc⟩ := TailShell.bstar_shell_strat hx
  obtain ⟨h1, h2⟩ := TailShell.toZModPow_shift (v := m + 3) (by omega) x
  refine TailShell.bstar_mem_shell ?_ hUp' ?_ ?_
  · rw [mem_bStarTailLocus_iff, h1, h2]
    exact mem_bStarTailLocus_iff.1 hx.1
  · exact (TailShell.bstar_run_flip hx.1 (TailShell.bstar_shell_mem_nonsingularLocus hx) hκ hUp').1
  · exact ((TailShell.bstar_run_flip hx.1 (TailShell.bstar_shell_mem_nonsingularLocus hx) hκ
      hUp').2).2 hc

/-- **The same shift sends the `c = 4` part into the `c = 2` part**, off the null set where the
image is singular. -/
theorem TailShell.bstar_shell_four_subset {m : ℕ} (hm : 2 ≤ m) :
    bStarTailShell m 4 ∩ TailShell.shift (m + 3) ⁻¹' nonsingularLocus 2
      ⊆ TailShell.shift (m + 3) ⁻¹' bStarTailShell m 2 := by
  intro x ⟨hx, hUp'⟩
  obtain ⟨hκ, hc⟩ := TailShell.bstar_shell_strat hx
  obtain ⟨h1, h2⟩ := TailShell.toZModPow_shift (v := m + 3) (by omega) x
  have hxc : TailShell.shift (m + 3) x ∈ bStarTailLocus := by
    rw [mem_bStarTailLocus_iff, h1, h2]
    exact mem_bStarTailLocus_iff.1 hx.1
  obtain ⟨hκ', hiff⟩ :=
    TailShell.bstar_run_flip hx.1 (TailShell.bstar_shell_mem_nonsingularLocus hx) hκ hUp'
  obtain ⟨-, hor⟩ := bstarTail_exists_kodairaSymbol_and_tamagawaNumber hxc hUp'
  refine TailShell.bstar_mem_shell hxc hUp' hκ' ?_
  rcases hor with h | h
  · exact h
  · exact absurd (hiff.1 h) (by rw [hc]; exact fun h4 => absurd h4 (by decide))

/-- **The two parts of one shell have equal mass**: for `m ≥ 2`, the shells `bStarTailShell m 2`
and `bStarTailShell m 4` have the same volume. -/
theorem TailShell.bstar_volume_shell_eq {m : ℕ} (hm : 2 ≤ m) :
    (volume : Measure (ℤ_[2] × ℤ_[2])) (bStarTailShell m 2)
      = volume (bStarTailShell m 4) := by
  have key : ∀ c c' : ℕ, (bStarTailShell m c ∩ TailShell.shift (m + 3) ⁻¹' nonsingularLocus 2
      ⊆ TailShell.shift (m + 3) ⁻¹' bStarTailShell m c') →
      (volume : Measure (ℤ_[2] × ℤ_[2])) (bStarTailShell m c)
        ≤ volume (bStarTailShell m c') := by
    intro c c' hsub
    have hcover : bStarTailShell m c
        ⊆ (bStarTailShell m c ∩ TailShell.shift (m + 3) ⁻¹' nonsingularLocus 2)
          ∪ TailShell.shift (m + 3) ⁻¹' (nonsingularLocus 2)ᶜ := by
      intro y hy
      by_cases h : TailShell.shift (m + 3) y ∈ nonsingularLocus 2
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr h
    refine le_trans (measure_mono hcover) (le_trans (measure_union_le _ _) ?_)
    rw [TailShell.volume_preimage_compl_nonsingularLocus, add_zero]
    refine le_trans (measure_mono hsub) (le_of_eq ?_)
    rw [TailShell.volume_preimage_shift]
  exact le_antisymm (key 2 4 (TailShell.bstar_shell_two_subset hm))
    (key 4 2 (TailShell.bstar_shell_four_subset hm))

/-- **The shell of level `m` is empty when `m < 2`.** -/
theorem TailShell.bstar_shell_eq_empty {m : ℕ} (hm : m < 2) (c : ℕ) :
    bStarTailShell m c = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨hκ, -⟩ := TailShell.bstar_shell_strat hx
  obtain ⟨m', hm', hκ'⟩ :=
    TailShell.bstar_exists_two_le_kodairaSymbol hx.1 (TailShell.bstar_shell_mem_nonsingularLocus hx)
  obtain rfl : m' = m := KodairaSymbol.I!.inj (hκ'.symm.trans hκ)
  omega

/-! ### `BStarTailFlip` -/

/-- **`BStarTailFlip`**: the two Tamagawa halves of the deep cylinder `a₄ ≡ 20`, `a₆ ≡ 16 (mod 32)`
have equal mass. Each half is the disjoint union of its level shells, and the shells of level `m`
in the two halves have equal mass, both being empty for `m < 2`. -/
theorem TailShell.bstarTailFlip : BStarTailFlip := by
  rw [BStarTailFlip, TailShell.bstar_iUnion_shell_two, TailShell.bstar_iUnion_shell_four,
    measure_iUnion (TailShell.bstar_pairwise_disjoint_shell 2)
      (fun m => measurableSet_bStarTailShell m 2),
    measure_iUnion (TailShell.bstar_pairwise_disjoint_shell 4)
      (fun m => measurableSet_bStarTailShell m 4)]
  refine tsum_congr fun m => ?_
  by_cases hm : 2 ≤ m
  · exact TailShell.bstar_volume_shell_eq hm
  · rw [TailShell.bstar_shell_eq_empty (by omega) 2,
      TailShell.bstar_shell_eq_empty (by omega) 4]

/-! ### The shells of the odd tail cylinder -/

open scoped Classical in
/-- **On the odd tail cylinder the reported index is at least `2`.**
`exists_step7_entry_aStarTail` supplies the entry model whose `a₃` is divisible by `8`, which is
the double root the level bound needs. -/
theorem TailShell.astar_exists_two_le_kodairaSymbol {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ aStarTailLocus) (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) :
    ∃ m, 2 ≤ m ∧ (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! m := by
  classical
  obtain ⟨h1, h2⟩ := aStarTailRes_congr _ _ (mem_aStarTailLocus_iff.1 hx)
  obtain ⟨A, E, ha₄, ha₆⟩ := exists_params_AStarTail h1 (by
    rw [show PadicInt.toZModPow 5 x.2 - PadicInt.toZModPow 5 x.1 - 5
      = (PadicInt.toZModPow 5 x.2, PadicInt.toZModPow 5 x.1).1
        - (PadicInt.toZModPow 5 x.2, PadicInt.toZModPow 5 x.1).2 - 5 from rfl]
    exact h2)
  obtain ⟨V, R, S, μ, h5, hdbl, hntr, hW₇⟩ :=
    exists_step7_entry_aStarTail (p := 2) rfl (by norm_num) ha₄ ha₆
  refine TailShell.exists_two_le_kodairaSymbol_of_hasDoubleRoot hΔ h5 hdbl hntr ?_
  rw [hW₇]
  exact TailShell.hasDoubleRoot_quadratic_entry_even (p := 2) rfl (by norm_num) _ _ R S μ

/-- **The shell of level `m` and Tamagawa number `c`** of the odd tail cylinder. -/
noncomputable def aStarTailShell (m c : ℕ) : Set (ℤ_[2] × ℤ_[2]) :=
  aStarTailLocus ∩ stratFibre 2 (KodairaSymbol.I! m, c)

/-- The shell `aStarTailShell m c` is measurable. -/
theorem measurableSet_aStarTailShell (m c : ℕ) : MeasurableSet (aStarTailShell m c) :=
  measurableSet_aStarTailLocus.inter (isOpen_stratFibre (p := 2) _).measurableSet

/-- Every point of the odd tail's shell `aStarTailShell m c` is nonsingular. -/
theorem TailShell.astar_shell_mem_nonsingularLocus {m c : ℕ} {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ aStarTailShell m c) : x ∈ nonsingularLocus 2 := stratFibre_subset _ hx.2

/-- The reduction datum of a point of the odd tail's shell of level `m`, read off. -/
theorem TailShell.astar_shell_strat {m c : ℕ} {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ aStarTailShell m c) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero (TailShell.astar_shell_mem_nonsingularLocus hx)).kodairaSymbol
          = KodairaSymbol.I! m ∧
      (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero
          (TailShell.astar_shell_mem_nonsingularLocus hx)).tamagawaNumber = c := by
  have h := (mem_stratFibre_iff (TailShell.astar_shell_mem_nonsingularLocus hx)).1 hx.2
  rw [strat] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- A nonsingular point of the odd tail cylinder whose reduction datum is `(Iₘ*, c)` lies in
`aStarTailShell m c`. -/
theorem TailShell.astar_mem_shell {m c : ℕ} {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ aStarTailLocus)
    (hUp : x ∈ nonsingularLocus 2)
    (hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = KodairaSymbol.I! m)
    (hc : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hUp).tamagawaNumber = c) :
    x ∈ aStarTailShell m c :=
  ⟨hx, (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hκ hc)⟩

/-- **The odd tail's symbol and Tamagawa number**: every nonsingular point of the odd tail
cylinder has symbol `Iₘ*` with `m ≠ 0` and Tamagawa number `2` or `4`. -/
theorem TailShell.astar_exists_kodairaSymbol_and_tamagawaNumber {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ aStarTailLocus) (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) :
    (∃ m, m ≠ 0 ∧ (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I! m) ∧
      ((TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 2 ∨
        (TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 4) := by
  obtain ⟨h1, h2⟩ := aStarTailRes_congr _ _ (mem_aStarTailLocus_iff.1 hx)
  obtain ⟨A, E, ha₄, ha₆⟩ := exists_params_AStarTail h1 (by
    rw [show PadicInt.toZModPow 5 x.2 - PadicInt.toZModPow 5 x.1 - 5
      = (PadicInt.toZModPow 5 x.2, PadicInt.toZModPow 5 x.1).1
        - (PadicInt.toZModPow 5 x.2, PadicInt.toZModPow 5 x.1).2 - 5 from rfl]
    exact h2)
  obtain ⟨V, h5, hdbl, hntr⟩ := exists_step5_cubic_aStarTail (p := 2) rfl (by norm_num) ha₄ ha₆
  exact run_eq_AStarTail_of_step5 hΔ h5 hdbl hntr

/-- **The `c = 2` half of the odd tail is exactly the union of its shells.** -/
theorem TailShell.astar_iUnion_shell_two :
    aStarTailTwoLocus = ⋃ m, aStarTailShell m 2 := by
  refine Set.eq_of_subset_of_subset (fun x hx => ?_) (Set.iUnion_subset fun m y hy => ?_)
  · obtain ⟨hxc, hst⟩ := hx
    obtain ⟨κ, hκ⟩ := Set.mem_iUnion.1 hst
    have hUp : x ∈ nonsingularLocus 2 := stratFibre_subset _ hκ
    obtain ⟨⟨m, -, hm⟩, -⟩ :=
      TailShell.astar_exists_kodairaSymbol_and_tamagawaNumber hxc hUp
    have h := (mem_stratFibre_iff hUp).1 hκ
    rw [strat] at h
    exact Set.mem_iUnion.2 ⟨m, TailShell.astar_mem_shell hxc hUp hm (congrArg Prod.snd h)⟩
  · exact ⟨hy.1, Set.mem_iUnion.2 ⟨KodairaSymbol.I! m, hy.2⟩⟩

/-- **The `c = 4` half of the odd tail is exactly the union of its shells.** -/
theorem TailShell.astar_iUnion_shell_four :
    aStarTailFourLocus = ⋃ m, aStarTailShell m 4 := by
  refine Set.eq_of_subset_of_subset (fun x hx => ?_) (Set.iUnion_subset fun m y hy => ?_)
  · obtain ⟨hxc, hst⟩ := hx
    obtain ⟨κ, hκ⟩ := Set.mem_iUnion.1 hst
    have hUp : x ∈ nonsingularLocus 2 := stratFibre_subset _ hκ
    obtain ⟨⟨m, -, hm⟩, -⟩ :=
      TailShell.astar_exists_kodairaSymbol_and_tamagawaNumber hxc hUp
    have h := (mem_stratFibre_iff hUp).1 hκ
    rw [strat] at h
    exact Set.mem_iUnion.2 ⟨m, TailShell.astar_mem_shell hxc hUp hm (congrArg Prod.snd h)⟩
  · exact ⟨hy.1, Set.mem_iUnion.2 ⟨KodairaSymbol.I! m, hy.2⟩⟩

/-- For fixed `c`, the odd tail's shells `aStarTailShell m c` are pairwise disjoint in `m`. -/
theorem TailShell.astar_pairwise_disjoint_shell (c : ℕ) :
    Pairwise (Function.onFun Disjoint fun m => aStarTailShell m c) := by
  intro m m' hmm
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  exact (Set.disjoint_left.1 (disjoint_stratFibre_of_ne (p := 2)
    (κ := KodairaSymbol.I! m) (κ' := KodairaSymbol.I! m')
    (fun h => hmm (KodairaSymbol.I!.inj h)) c c) hx.2) hx'.2

open scoped Classical in
/-- **The flip on the odd tail cylinder**, at the shift the shell's own level dictates. -/
theorem TailShell.astar_run_flip {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ aStarTailLocus) {m : ℕ}
    (hUp : x ∈ nonsingularLocus 2)
    (hκ : (TateAlgorithm.run (W := ofShortNF x.1 x.2)
      PadicInt.uniformizer_ne_zero hUp).kodairaSymbol = KodairaSymbol.I! m)
    (hΔ' : (ofShortNF x.1 (x.2 + ((2 : ℕ) : ℤ_[2]) ^ (m + 3))).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF x.1 (x.2 + ((2 : ℕ) : ℤ_[2]) ^ (m + 3)))
        PadicInt.uniformizer_ne_zero hΔ').kodairaSymbol = KodairaSymbol.I! m ∧
      ((TateAlgorithm.run (W := ofShortNF x.1 (x.2 + ((2 : ℕ) : ℤ_[2]) ^ (m + 3)))
          PadicInt.uniformizer_ne_zero hΔ').tamagawaNumber = 4 ↔
        (TateAlgorithm.run (W := ofShortNF x.1 x.2)
          PadicInt.uniformizer_ne_zero hUp).tamagawaNumber = 2) := by
  classical
  obtain ⟨h1, h2⟩ := aStarTailRes_congr _ _ (mem_aStarTailLocus_iff.1 hx)
  obtain ⟨A, E, ha₄, ha₆⟩ := exists_params_AStarTail h1 (by
    rw [show PadicInt.toZModPow 5 x.2 - PadicInt.toZModPow 5 x.1 - 5
      = (PadicInt.toZModPow 5 x.2, PadicInt.toZModPow 5 x.1).1
        - (PadicInt.toZModPow 5 x.2, PadicInt.toZModPow 5 x.1).2 - 5 from rfl]
    exact h2)
  obtain ⟨V, h5, hdbl, hntr⟩ := exists_step5_cubic_aStarTail (p := 2) rfl (by norm_num) ha₄ ha₆
  exact FlipRun.run_flip_ofShortNF (p := 2) rfl hUp hΔ' h5 hdbl hntr hκ rfl

/-- **An offset `2^v` with `5 ≤ v` leaves the odd tail's four residue classes alone.** -/
theorem TailShell.astar_mem_locus_shift {v : ℕ} (hv : 5 ≤ v) {x : ℤ_[2] × ℤ_[2]}
    (hx : x ∈ aStarTailLocus) : TailShell.shift v x ∈ aStarTailLocus := by
  obtain ⟨h1, h2⟩ := TailShell.toZModPow_shift hv x
  rw [mem_aStarTailLocus_iff, h1, h2]
  exact mem_aStarTailLocus_iff.1 hx

/-- **The shift sends the `c = 2` part of an odd-tail shell into its `c = 4` part.** -/
theorem TailShell.astar_shell_two_subset {m : ℕ} (hm : 2 ≤ m) :
    aStarTailShell m 2 ∩ TailShell.shift (m + 3) ⁻¹' nonsingularLocus 2
      ⊆ TailShell.shift (m + 3) ⁻¹' aStarTailShell m 4 := by
  intro x ⟨hx, hUp'⟩
  obtain ⟨hκ, hc⟩ := TailShell.astar_shell_strat hx
  refine TailShell.astar_mem_shell
    (TailShell.astar_mem_locus_shift (by omega) hx.1) hUp' ?_ ?_
  · exact (TailShell.astar_run_flip hx.1 (TailShell.astar_shell_mem_nonsingularLocus hx) hκ hUp').1
  · exact ((TailShell.astar_run_flip hx.1 (TailShell.astar_shell_mem_nonsingularLocus hx) hκ
      hUp').2).2 hc

/-- **The same shift sends the odd tail's `c = 4` part into its `c = 2` part.** -/
theorem TailShell.astar_shell_four_subset {m : ℕ} (hm : 2 ≤ m) :
    aStarTailShell m 4 ∩ TailShell.shift (m + 3) ⁻¹' nonsingularLocus 2
      ⊆ TailShell.shift (m + 3) ⁻¹' aStarTailShell m 2 := by
  intro x ⟨hx, hUp'⟩
  obtain ⟨hκ, hc⟩ := TailShell.astar_shell_strat hx
  have hxc : TailShell.shift (m + 3) x ∈ aStarTailLocus :=
    TailShell.astar_mem_locus_shift (by omega) hx.1
  obtain ⟨hκ', hiff⟩ :=
    TailShell.astar_run_flip hx.1 (TailShell.astar_shell_mem_nonsingularLocus hx) hκ hUp'
  obtain ⟨-, hor⟩ := TailShell.astar_exists_kodairaSymbol_and_tamagawaNumber hxc hUp'
  refine TailShell.astar_mem_shell hxc hUp' hκ' ?_
  rcases hor with h | h
  · exact h
  · exact absurd (hiff.1 h) (by rw [hc]; exact fun h4 => absurd h4 (by decide))

/-- **The two parts of one odd-tail shell have equal mass.** -/
theorem TailShell.astar_volume_shell_eq {m : ℕ} (hm : 2 ≤ m) :
    (volume : Measure (ℤ_[2] × ℤ_[2])) (aStarTailShell m 2)
      = volume (aStarTailShell m 4) := by
  have key : ∀ c c' : ℕ, (aStarTailShell m c ∩ TailShell.shift (m + 3) ⁻¹' nonsingularLocus 2
      ⊆ TailShell.shift (m + 3) ⁻¹' aStarTailShell m c') →
      (volume : Measure (ℤ_[2] × ℤ_[2])) (aStarTailShell m c)
        ≤ volume (aStarTailShell m c') := by
    intro c c' hsub
    have hcover : aStarTailShell m c
        ⊆ (aStarTailShell m c ∩ TailShell.shift (m + 3) ⁻¹' nonsingularLocus 2)
          ∪ TailShell.shift (m + 3) ⁻¹' (nonsingularLocus 2)ᶜ := by
      intro y hy
      by_cases h : TailShell.shift (m + 3) y ∈ nonsingularLocus 2
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr h
    refine le_trans (measure_mono hcover) (le_trans (measure_union_le _ _) ?_)
    rw [TailShell.volume_preimage_compl_nonsingularLocus, add_zero]
    refine le_trans (measure_mono hsub) (le_of_eq ?_)
    rw [TailShell.volume_preimage_shift]
  exact le_antisymm (key 2 4 (TailShell.astar_shell_two_subset hm))
    (key 4 2 (TailShell.astar_shell_four_subset hm))

/-- **The odd tail's shell of level `m` is empty when `m < 2`.** -/
theorem TailShell.astar_shell_eq_empty {m : ℕ} (hm : m < 2) (c : ℕ) :
    aStarTailShell m c = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨hκ, -⟩ := TailShell.astar_shell_strat hx
  obtain ⟨m', hm', hκ'⟩ :=
    TailShell.astar_exists_two_le_kodairaSymbol hx.1 (TailShell.astar_shell_mem_nonsingularLocus hx)
  obtain rfl : m' = m := KodairaSymbol.I!.inj (hκ'.symm.trans hκ)
  omega

/-- **The odd tail's two Tamagawa halves have equal mass.** -/
theorem TailShell.astarTailFlip :
    (volume : Measure (ℤ_[2] × ℤ_[2])) aStarTailTwoLocus
      = volume aStarTailFourLocus := by
  rw [TailShell.astar_iUnion_shell_two, TailShell.astar_iUnion_shell_four,
    measure_iUnion (TailShell.astar_pairwise_disjoint_shell 2)
      (fun m => measurableSet_aStarTailShell m 2),
    measure_iUnion (TailShell.astar_pairwise_disjoint_shell 4)
      (fun m => measurableSet_aStarTailShell m 4)]
  refine tsum_congr fun m => ?_
  by_cases hm : 2 ≤ m
  · exact TailShell.astar_volume_shell_eq hm
  · rw [TailShell.astar_shell_eq_empty (by omega) 2,
      TailShell.astar_shell_eq_empty (by omega) 4]

/-! ### The mass of each half of the odd tail -/

/-- **Each half of the odd tail has mass `2⁻⁹ = 1/512`**: the two are equal and together they carry
the cylinder's whole mass `1/256`, the singular locus being null. -/
theorem TailShell.astar_volume_eq :
    (volume : Measure (ℤ_[2] × ℤ_[2])) aStarTailTwoLocus = 1 / 512 ∧
      (volume : Measure (ℤ_[2] × ℤ_[2])) aStarTailFourLocus = 1 / 512 := by
  have hle := le_volume_aStarTailTwoLocus_add_volume_aStarTailFourLocus
  have hge : (volume : Measure (ℤ_[2] × ℤ_[2])) aStarTailTwoLocus
      + volume aStarTailFourLocus ≤ 1 / 256 := by
    rw [← measure_union disjoint_aStarTailTwoLocus_aStarTailFourLocus
      measurableSet_aStarTailFourLocus, ← volume_aStarTailLocus]
    exact measure_mono (Set.union_subset (fun _ hx => hx.1) fun _ hx => hx.1)
  have hsum : (volume : Measure (ℤ_[2] × ℤ_[2])) aStarTailTwoLocus
      + volume aStarTailFourLocus = 1 / 256 := le_antisymm hge hle
  rw [TailShell.astarTailFlip, ← two_mul] at hsum
  have h : (volume : Measure (ℤ_[2] × ℤ_[2])) aStarTailFourLocus = 1 / 512 := by
    refine (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).1 ?_
    rw [hsum, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
      show (512 : ℝ≥0∞) = 2 * 256 by norm_num,
      ENNReal.mul_inv (by norm_num) (by norm_num), mul_one, mul_one, ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  exact ⟨by rw [TailShell.astarTailFlip]; exact h, h⟩

end WeierstrassCurve

end
