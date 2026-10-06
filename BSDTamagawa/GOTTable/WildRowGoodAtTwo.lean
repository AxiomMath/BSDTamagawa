/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildRowLowerBound
public import BSDTamagawa.NumberTheory.SplitStoreyDescentTwo

/-!
# The good-reduction stratum `(I_0, 1)` at `p = 2`, on the split-congruence locus

On the residue cylinder `a₄ = 5 + 16α`, `a₆ = 2(11 + 8α + 32k)` over `ℤ_2`, Steps 1–10 of Tate's
algorithm all fall through and Step 11 divides the model down, at every level. On this family

  `Δ = -64(a₄³ + 27b²) = -2¹² · (53 + 93α + 87α² + 64α³ + 297k + 216αk + 432k²)`

with `a₆ = 2b`, and the second factor is `≡ 1 + k` modulo `2`. Taking `k = 2w` makes it
`1 + 2(26 + 3α + 87m + 32α³ + 297w + 216αw + 864w²)` with `α² + α = 2m`, which is odd, so
`Δ = -2¹² u` with `u` a unit, the descended model `V` has `Δ(V) = -u` a unit, and Step 1 of the
next round answers `(I_0, 1)`.

Modulo `2 ^ 7` the even-`k` half is the eight classes

  `(a₄, a₆) ≡ (5, 22), (21, 38), (37, 54), (53, 70), (69, 86), (85, 102), (101, 118), (117, 6)`,

i.e. `a₄ ≡ 5 mod 16` together with `a₆ ≡ a₄ + 17 mod 128`, of mass `8 · 2⁻¹⁴ = 1/2048`. This is a
quarter of the `(I_0, 1)` stratum, whose minimal mass is `1/512`.

## Main definitions

* `WeierstrassCurve.headResGoodTwo`: the eight residue classes modulo `2 ^ 7`.
* `WeierstrassCurve.good2Locus`: the corresponding cylinder in `ℤ_2²`.

## Main results

* `WeierstrassCurve.TateAlgorithm.Step11.run_eq_ok_of_params_two`: Steps 1–10 of Tate's algorithm
  do not answer on `a₄ = 5 + 16α`, `a₆ = 2(11 + 8α + 32k)`, at every level, so Step 11 fires.
* `WeierstrassCurve.volume_good2Locus`: the cylinder has mass `1/2048`.
* `WeierstrassCurve.run_eq_I0_of_mem_good2Locus`: on it Tate's algorithm answers `(I_0, 1)`.
* `WeierstrassCurve.good2Locus_subset_headMinimal`: it lies in the minimal part of the `t = 1` row.
-/

open scoped ENNReal
open MeasureTheory Set CommRing Ideal

@[expose] public section

namespace WeierstrassCurve

open TateAlgorithm BSDTamagawa.LocalConstancy

namespace TateAlgorithm

variable {p : ℕ} [Fact p.Prime]

/-! ### Exact division -/

/-- Exact division by the uniformiser. -/
private theorem div_eq_of_eq_mul {x a : ℤ_[p]} (h : x = (p : ℤ_[p]) * a) :
    div x (p : ℤ_[p]) = a := by
  subst h
  exact mul_left_cancel₀ PadicInt.uniformizer_ne_zero
    (CommRing.mul_div PadicInt.uniformizer_ne_zero (Dvd.intro a rfl))

/-- Equal residues from a divisible difference. -/
private theorem mod_eq_mod_of_dvd_sub {x y : ℤ_[p]} (h : (p : ℤ_[p]) ∣ x - y) :
    mod (p : ℤ_[p]) x = mod (p : ℤ_[p]) y := by
  rw [← sub_eq_zero, ← map_sub, mod_eq_zero]; exact h

/-! ### Steps 1–10 on the parametrised split locus, at every level -/

/-- **Steps 1–10 of Tate's algorithm cannot answer on a short model over `ℤ_2` with `a₄ = 5 + 16α`
and `a₆ = 2(11 + 8α + 32k)`, so Step 11 fires.** No hypothesis on `v₂(Δ)` is needed; in particular
`v₂(Δ) = 12` is allowed. -/
theorem Step11.run_eq_ok_of_params_two (hp2 : p = 2) {a₄ a₆ b α k : ℤ_[p]}
    (hΔ0 : (ofShortNF a₄ a₆).Δ ≠ 0) (ha₆' : a₆ = 2 * b) (ha₄u : IsUnit a₄)
    (ha₄ : a₄ = 5 + 16 * α) (hb : b = 11 + 8 * α + 32 * k) :
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
      ⟨b + 3 + 8 * α + 8 * ρ + 16 * α * ρ + 6 * ρ ^ 2 + 4 * ρ ^ 3, by
        rw [hπ, ha₆', ha₄, hr]; ring⟩
    have h3 : (p : ℤ_[p]) ∣ t ^ 2 := by
      have h := dvd_sub h2 hva₆
      rwa [show a₆ + r * a₄ + r ^ 3 - (a₆ + r * a₄ + r ^ 3 - t ^ 2) = t ^ 2 from by ring] at h
    obtain ⟨τ, hτ⟩ := PadicInt.prime_p.dvd_of_dvd_pow h3
    exact ⟨τ, by rw [hτ, hπ]⟩
  obtain ⟨mτ, hmτ⟩ := exists_sq_add_self_eq_two_mul hp2 hπ τ
  obtain ⟨Q₄, hQ₄⟩ : ∃ x : ℤ_[p], x = 1 + 2 * α + 3 * m := ⟨_, rfl⟩
  obtain ⟨Q₆, hQ₆⟩ : ∃ x : ℤ_[p],
      x = 7 + 8 * α + 16 * k + 3 * ρ + 8 * α * ρ + 2 * m + 4 * ρ * m - τ ^ 2 := ⟨_, rfl⟩
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
    refine ⟨3 + 4 * α + 8 * k + ρ + 4 * α * ρ + m + 2 * ρ * m + τ - mτ + j, ?_⟩
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
  obtain ⟨X₆, hX₆⟩ : ∃ x : ℤ_[p], x = 3 + 4 * α + 8 * k + ρ + 4 * α * ρ + 2 * ρ * m
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
    rw [div_eq_of_eq_mul hV2a₂]
    exact mod_eq_mod_of_dvd_sub ⟨ρ - 2 * mσ, by rw [hπ, hX₂]; ring⟩
  have hcc : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).c
      = mod (p : ℤ_[p]) (1 + ρ) := by
    change mod (p : ℤ_[p]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₄)
      ((p : ℤ_[p]) ^ 2)) = _
    rw [div_eq_of_eq_pow_mul_two hV2a₄]
    exact mod_eq_mod_of_dvd_sub
      ⟨2 * α + 3 * m - ρ - θ - σ * (1 + ρ + 2 * θ), by rw [hπ, hX₄, hQ₄]; ring⟩
  have hcd : (cubic (p : ℤ_[p]) ((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆) 1 1).d
      = mod (p : ℤ_[p]) (1 + ρ) := by
    change mod (p : ℤ_[p]) (div (((VariableChange.mk 1 r s T₂) • ofShortNF a₄ a₆).a₆)
      ((p : ℤ_[p]) ^ 3)) = _
    rw [div_eq_of_eq_pow_mul_two hV2a₆]
    exact mod_eq_mod_of_dvd_sub
      ⟨1 + 2 * α + 4 * k + 2 * α * ρ + ρ * m - θ - ρ * θ - θ ^ 2, by rw [hπ, hX₆]; ring⟩
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
      rw [← mod_eq_zero, map_sub, hr₈def, Step8.mod_r_two hp2, div_eq_of_eq_mul hV2a₂, sub_self]
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
  obtain ⟨E, hE⟩ : ∃ x : ℤ_[p], x = 1 + 4 * k - 2 * ψ - 4 * α * ψ - 3 * ψ ^ 2 - 4 * ψ ^ 3
      - v ^ 2 := ⟨_, rfl⟩
  have hV3a₃ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₃ = (p : ℤ_[p]) ^ 3 * v := by
    rw [smul_ofShortNF_a₃, hT₃, hπ]; ring
  have hV3a₆ : ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆).a₆ = (p : ℤ_[p]) ^ 4 * E := by
    rw [smul_ofShortNF_a₆, hR₃, hT₃, hπ, ha₆', hb, ha₄, hE]; ring
  have hqc : (quadratic (p : ℤ_[p]) ((VariableChange.mk 1 R₃ s T₃) • ofShortNF a₄ a₆) 2).c = 0 := by
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
  obtain ⟨lam, hlam⟩ : ∃ l : ℤ_[p], v + tY = 1 + ψ + 2 * l := by
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
    refine ⟨mv + 3 * mψ - ψ - 1 - 2 * k + 2 * α * ψ + 2 * ψ ^ 3 + j, ?_⟩
    linear_combination hj + hmv + 3 * hmψ
  obtain ⟨T₄, hT₄⟩ : ∃ x : ℤ_[p], x = (p : ℤ_[p]) ^ 2 * (1 + ψ + 2 * lam) := ⟨_, rfl⟩
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
      = (p : ℤ_[p]) ^ 4 * (α + ψ + 3 * ψ ^ 2 - lam - σ * (1 + ψ + 2 * lam)) := by
    rw [smul_ofShortNF_a₄, hR₃, hT₄, hπ, ha₄, hs2]; ring
  have hV4a₆ : ((VariableChange.mk 1 R₃ s T₄) • ofShortNF a₄ a₆).a₆
      = (p : ℤ_[p]) ^ 6 * (k - ψ - α * ψ - ψ ^ 2 - ψ ^ 3 - lam - lam * ψ - lam ^ 2) := by
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

/-! ### An oddness criterion -/

/-- An element of `ℤ_2` of the form `1 + 2y` is not divisible by `2`. -/
theorem not_dvd_of_eq_one_add_two_mul {z y : ℤ_[2]} (h : z = 1 + 2 * y) :
    ¬ ((2 : ℕ) : ℤ_[2]) ∣ z := by
  intro hd
  have hy : ((2 : ℕ) : ℤ_[2]) ∣ 2 * y := ⟨y, by norm_num⟩
  have h1 : ((2 : ℕ) : ℤ_[2]) ∣ (1 : ℤ_[2]) := by
    have hs := dvd_sub hd hy
    rwa [h, add_sub_cancel_right] at hs
  exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_one h1)

/-! ### The eight-class cylinder -/

/-- The eight residue classes modulo `2 ^ 7` carrying the split-congruence quarter of the
`(I_0, 1)` stratum: `a₄ ≡ 5 mod 16` together with `a₆ ≡ a₄ + 17 mod 128`. -/
def headResGoodTwo : Finset (ZMod (2 ^ 7) × ZMod (2 ^ 7)) :=
  {(5, 22), (21, 38), (37, 54), (53, 70), (69, 86), (85, 102), (101, 118), (117, 6)}

/-- The set `headResGoodTwo` consists of exactly eight residue classes. -/
theorem card_headResGoodTwo : headResGoodTwo.card = 8 := by decide

/-- The two congruences the eight classes satisfy: `16 ∣ a₄ - 5`, written `2 ^ 7 ∣ 8(a₄ - 5)`, and
`2 ^ 7 ∣ a₆ - a₄ - 17`. -/
theorem headResGoodTwo_spec :
    ∀ c ∈ headResGoodTwo, 8 * (c.1 - 5) = 0 ∧ c.2 - c.1 - 17 = 0 := by
  intro c hc
  simp only [headResGoodTwo, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- The **good-reduction locus** at `2`: the eight residue classes modulo `2 ^ 7`. -/
noncomputable def good2Locus : Set (ℤ_[2] × ℤ_[2]) :=
  PadicInt.redPairPow 2 7 ⁻¹' (headResGoodTwo : Set (ZMod (2 ^ 7) × ZMod (2 ^ 7)))

/-- A pair `(a₄, a₆)` lies in `good2Locus` if and only if its reduction modulo `2 ^ 7` lies in
`headResGoodTwo`. -/
theorem mem_good2Locus_iff {x : ℤ_[2] × ℤ_[2]} :
    x ∈ good2Locus ↔
      (PadicInt.toZModPow 7 x.1, PadicInt.toZModPow 7 x.2) ∈ headResGoodTwo := by
  rw [good2Locus, mem_preimage, Finset.mem_coe, PadicInt.redPairPow]

/-- The set `good2Locus` is measurable. -/
theorem measurableSet_good2Locus : MeasurableSet good2Locus :=
  PadicInt.measurableSet_preimage_redPairPow 7 headResGoodTwo

/-- `8 · 2⁻¹⁴ = 8/16384 = 1/2048`. -/
theorem eight_mul_inv_pow_fourteen_div_eq :
    ((8 : ℕ) : ℝ≥0∞) * ((((2 : ℕ)) : ℝ≥0∞)⁻¹) ^ (2 * 7) = 1 / 2048 := by
  rw [show ((8 : ℕ) : ℝ≥0∞) = 8 by norm_num, show (((2 : ℕ)) : ℝ≥0∞) = 2 by norm_num,
    ← ENNReal.inv_pow, show ((2 : ℝ≥0∞)) ^ (2 * 7) = 16384 by norm_num, ← div_eq_mul_inv]
  exact enn_div_eq_div (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The mass of the good-reduction locus at `2` is `8/16384 = 1/2048`.** -/
theorem volume_good2Locus : (volume : Measure (ℤ_[2] × ℤ_[2])) good2Locus = 1 / 2048 := by
  rw [good2Locus, PadicInt.volume_preimage_redPairPow, card_headResGoodTwo,
    eight_mul_inv_pow_fourteen_div_eq]

/-! ### The parameters and the discriminant the cylinder carries -/

/-- **The locus is the parametrised split family with `k` even, and there `v₂(Δ) = 12`.** From
`2 ^ 7 ∣ 8(a₄ - 5)` one gets `a₄ = 5 + 16α`, and `2 ^ 7 ∣ a₆ - a₄ - 17` then gives
`a₆ = 2(11 + 8α + 64w)`; on that family `Δ = -2¹²(1 + 2z)` with
`z = 26 + 3α + 87m + 32α³ + 297w + 216αw + 864w²` and `α² + α = 2m`. -/
theorem exists_params_of_mem_good2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ good2Locus) :
    ∃ α w z : ℤ_[2], x.1 = 5 + 16 * α ∧ x.2 = 2 * (11 + 8 * α + 32 * (2 * w)) ∧
      (ofShortNF x.1 x.2).Δ = -4096 * (1 + 2 * z) := by
  obtain ⟨h8, h17⟩ := headResGoodTwo_spec _ (mem_good2Locus_iff.1 hx)
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have hd1 : ((2 : ℕ) : ℤ_[2]) ^ 7 ∣ 8 * (x.1 - 5) := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_mul, map_sub, map_ofNat, map_ofNat]
    exact h8
  have hd2 : ((2 : ℕ) : ℤ_[2]) ^ 7 ∣ x.2 - x.1 - 17 := by
    rw [PadicInt.pow_dvd_iff_toZModPow_eq_zero, map_sub, map_sub, map_ofNat]
    exact h17
  have h83 : (8 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 3 := by rw [hcast]; norm_num
  have hne : ((2 : ℕ) : ℤ_[2]) ^ 3 ≠ 0 := pow_ne_zero 3 PadicInt.uniformizer_ne_zero
  obtain ⟨α, hα⟩ : ((2 : ℕ) : ℤ_[2]) ^ 4 ∣ x.1 - 5 := by
    rw [h83, show (7 : ℕ) = 3 + 4 from rfl, pow_add, mul_dvd_mul_iff_left hne] at hd1
    exact hd1
  obtain ⟨w, hw⟩ := hd2
  rw [hcast] at hα hw
  obtain ⟨m, hm⟩ := TateAlgorithm.exists_sq_add_self_eq_two_mul (p := 2) rfl (by norm_num) α
  have hx1 : x.1 = 5 + 16 * α := by linear_combination hα
  have hx2 : x.2 = 2 * (11 + 8 * α + 32 * (2 * w)) := by linear_combination hw + hα
  refine ⟨α, w, 26 + 3 * α + 87 * m + 32 * α ^ 3 + 297 * w + 216 * α * w + 864 * w ^ 2,
    hx1, hx2, ?_⟩
  rw [ofShortNF_Δ, hx1, hx2]
  linear_combination (-356352 : ℤ_[2]) * hm

/-- No point of the good-reduction locus at `2` has an even `a₄`, so none is a dilate. -/
theorem notMem_range_of_mem_good2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ good2Locus) :
    x ∉ Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) := by
  obtain ⟨α, w, z, hα, hw, hΔ⟩ := exists_params_of_mem_good2Locus hx
  refine notMem_range_scaleProdByPPow_of_not_dvd_fst fun hdvd => ?_
  exact not_dvd_of_eq_one_add_two_mul (y := 2 + 8 * α) (by rw [hα]; ring)
    (dvd_trans (dvd_pow_self _ (by norm_num)) hdvd)

/-- The short model is nonsingular on the locus: `Δ = -2¹²(1 + 2z)` and `1 + 2z` is odd. -/
theorem Δ_ne_zero_of_mem_good2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ good2Locus) :
    (ofShortNF x.1 x.2).Δ ≠ 0 := by
  obtain ⟨α, w, z, hα, hw, hΔ⟩ := exists_params_of_mem_good2Locus hx
  rw [hΔ]
  refine mul_ne_zero (by norm_num) fun h0 => ?_
  exact not_dvd_of_eq_one_add_two_mul (z := 1 + 2 * z) (y := z) rfl (h0 ▸ dvd_zero _)

/-! ### Tate's algorithm on the locus -/

/-- **On the good-reduction locus Tate's algorithm answers `(I_0, 1)`.** Steps 1–10 fall through,
Step 11 divides the model down to `V` with `2¹² · Δ(V) = Δ`, and `Δ = -2¹²(1 + 2z)`, so
`Δ(V) = -(1 + 2z)` is a unit and Step 1 of the next round answers `(I_0, 1)`. -/
theorem run_eq_I0_of_mem_good2Locus {x : ℤ_[2] × ℤ_[2]} (hx : x ∈ good2Locus)
    (hΔ : (ofShortNF x.1 x.2).Δ ≠ 0) :
    (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ).kodairaSymbol = KodairaSymbol.I 0 ∧
      (TateAlgorithm.run (W := ofShortNF x.1 x.2)
        PadicInt.uniformizer_ne_zero hΔ).tamagawaNumber = 1 := by
  obtain ⟨α, w, z, hα, hw, hΔeq⟩ := exists_params_of_mem_good2Locus hx
  have hcast : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  have ha₄u : IsUnit x.1 := not_not.1 fun hnu =>
    not_dvd_of_eq_one_add_two_mul (y := 2 + 8 * α) (by rw [hα]; ring)
      (PadicInt.dvd_iff_not_isUnit.2 hnu)
  obtain ⟨V, hV⟩ := TateAlgorithm.Step11.run_eq_ok_of_params_two (p := 2) (α := α) (k := 2 * w)
    (b := 11 + 8 * α + 32 * (2 * w)) rfl hΔ hw ha₄u hα rfl
  have hΔV : ((2 : ℕ) : ℤ_[2]) ^ 12 * V.Δ = (ofShortNF x.1 x.2).Δ :=
    TateAlgorithm.Step11.run_Δ PadicInt.uniformizer_ne_zero hΔ hV
  have h4096 : ((2 : ℕ) : ℤ_[2]) ^ 12 = 4096 := by rw [hcast]; norm_num
  have hne : (4096 : ℤ_[2]) ≠ 0 := by
    rw [← h4096]; exact pow_ne_zero 12 PadicInt.uniformizer_ne_zero
  have hVΔ : V.Δ = -(1 + 2 * z) := by
    rw [h4096, hΔeq] at hΔV
    exact mul_left_cancel₀ hne (hΔV.trans (by ring))
  have hVdvd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ V.Δ :=
    not_dvd_of_eq_one_add_two_mul (y := -1 - z) (by rw [hVΔ]; ring)
  have hVne : V.Δ ≠ 0 := fun h0 => hVdvd (h0 ▸ dvd_zero _)
  have hs1 : TateAlgorithm.Step1.run ((2 : ℕ) : ℤ_[2]) V
      = Except.error ⟨V, KodairaSymbol.I 0, 1⟩ := by
    rw [TateAlgorithm.Step1.run.eq_def]; exact ite_eq_right hVdvd
  have hrun : TateAlgorithm.run (W := ofShortNF x.1 x.2) PadicInt.uniformizer_ne_zero hΔ
      = ⟨V, KodairaSymbol.I 0, 1⟩ := by
    rw [TateAlgorithm.run_eq_of_step11_ok PadicInt.uniformizer_ne_zero hΔ hV hVne]
    exact TateAlgorithm.run_eq_of_step11_error PadicInt.uniformizer_ne_zero hVne
      (step11_error_of_step2 hVne (step2_error_of_step1 hs1))
  exact ⟨by rw [hrun], by rw [hrun]⟩

/-! ### The locus in the `t = 1` row -/

/-- **The good-reduction locus at `2` lies in the strata over `t = 1`.** -/
theorem good2Locus_subset_iUnion_stratFibre :
    good2Locus ⊆ ⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1) := by
  intro x hx
  have hΔ : (ofShortNF x.1 x.2).Δ ≠ 0 := Δ_ne_zero_of_mem_good2Locus hx
  have hUp : x ∈ nonsingularLocus 2 := hΔ
  obtain ⟨hk, ht⟩ := run_eq_I0_of_mem_good2Locus hx hΔ
  exact Set.mem_iUnion.2 ⟨KodairaSymbol.I 0,
    (mem_stratFibre_iff hUp).2 (by rw [strat]; exact Prod.ext hk ht)⟩

/-- **The good-reduction locus at `2` lies in the minimal part of the `t = 1` row.** -/
theorem good2Locus_subset_headMinimal :
    good2Locus ⊆ (⋃ κ : KodairaSymbol, stratFibre 2 (κ, 1)) \
      Set.range (PadicInt.scaleProdByPPow 4 6 : ℤ_[2] × ℤ_[2] → ℤ_[2] × ℤ_[2]) :=
  fun _ hx => ⟨good2Locus_subset_iUnion_stratFibre hx, notMem_range_of_mem_good2Locus hx⟩

end WeierstrassCurve

end
