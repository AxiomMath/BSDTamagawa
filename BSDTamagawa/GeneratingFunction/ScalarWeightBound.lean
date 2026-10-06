/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Defs

/-!
# The scalar weight is bounded by `1` on `𝒟₀`

On the parameter region `𝒟₀` (that is, `Re(s) ≥ 0`, `|w| ≤ 1`, and `|z_ℓ| ≤ 1` for every `ℓ ∈ Π`)
the scalar weight satisfies `|ψ_{s, w, 𝐳}(t)| ≤ 1` for every integer `t ≥ 1`. Each of its three
factors is bounded by `1`: `‖w^{Ω(t)}‖ = ‖w‖^{Ω(t)}`, the product `∏_{ℓ ∈ Π} ‖z_ℓ‖^{v_ℓ(t)}` is a
finite product of numbers in `[0, 1]`, and `‖t^{-s}‖ = t^{-Re(s)} ≤ 1`.

## Main results

* `WeierstrassCurve.norm_scalarWeight_le_one`: `‖ψ_{s, w, 𝐳}(t)‖ ≤ 1` on `𝒟₀` for `t ≥ 1`.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

/-- If `Re(s) ≥ 0`, `‖w‖ ≤ 1` and `‖z_ℓ‖ ≤ 1` for every `ℓ ∈ Π`, then `‖ψ_{s, w, 𝐳}(t)‖ ≤ 1` for
every `t ≥ 1`. -/
@[bsd_tamagawa "T036f"]
theorem norm_scalarWeight_le_one (P : Finset ℕ) {s w : ℂ} {z : P → ℂ} {t : ℕ}
    (hs : 0 ≤ s.re) (hw : ‖w‖ ≤ 1) (hz : ∀ ℓ : P, ‖z ℓ‖ ≤ 1) (ht : 1 ≤ t) :
    ‖scalarWeight P s w z t‖ ≤ 1 := by
  have h₁ : ‖w ^ ArithmeticFunction.cardFactors t‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
  have h₂ : ‖multiMonomial (fun ℓ : P => padicValNat ℓ t) z‖ ≤ 1 := by
    rw [multiMonomial, norm_prod]
    exact Finset.prod_le_one₀ (fun ℓ _ => norm_nonneg _)
      fun ℓ _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hz ℓ)
  have h₃ : ‖(t : ℂ) ^ (-s)‖ ≤ 1 := by
    have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_le_one_of_one_le_of_nonpos ht1 (by rw [Complex.neg_re]; linarith)
  rw [scalarWeight, norm_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) h₁).trans h₂)).trans h₃

end WeierstrassCurve
