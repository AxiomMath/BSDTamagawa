/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.K0Mass

/-!
# The per-stratum bound for `δ_p(K)`

Every nontrivial reduction stratum carries mass `O(p^{-2})`, uniformly in the stratum and in the
prime:

  `δ_p(K) ≤ 9/p²` for every prime `p` and every `K ∈ 𝒦 ∖ 𝒦₀`,

where `𝒦₀ = {(I₀, 1), (I₁, 1)}`. The mass `δ_p(K)` is one term of the sum
`∑_{K' ∉ 𝒦₀} δ_p(K') = 1 - β_p`, which is at most `9/p²`.

## Main results

* `WeierstrassCurve.deltaP_le_nine_div_sq`: `δ_p(K) ≤ 9/p²` for every prime `p` and every `K ∉ 𝒦₀`.
* `WeierstrassCurve.exists_per_stratum_bound_deltaP`: there are `C > 0` and `p₀` with
  `δ_p(K) ≤ C/p²` for every prime `p ≥ p₀` and every `K ∉ 𝒦₀`.
-/

@[expose] public section

open scoped ENNReal

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction

variable (p : ℕ) [Fact p.Prime]

/-- `δ_p(K) ≤ 9/p²` for every prime `p` and every reduction datum `K ∈ 𝒦 ∖ 𝒦₀`. -/
@[bsd_tamagawa "T023f"]
theorem deltaP_le_nine_div_sq {K : ReductionData} (hK : K ∉ (K0 : Set ReductionData)) :
    deltaP p K ≤ 9 / (p : ℝ≥0∞) ^ 2 :=
  le_trans
    (ENNReal.le_tsum (f := fun K' : ↥(K0ᶜ : Set ReductionData) => deltaP p (K' : ReductionData))
      ⟨K, hK⟩)
    (tsum_compl_K0_le_nine_div_sq p)

/-- There are constants `C > 0` and `p₀` such that `δ_q(K) ≤ C/q²` for every prime `q ≥ p₀` and
every `K ∈ 𝒦 ∖ 𝒦₀`. -/
@[bsd_tamagawa "T023f"]
theorem exists_per_stratum_bound_deltaP :
    ∃ C : ℝ≥0∞, ∃ p₀ : ℕ, 0 < C ∧ ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q →
      ∀ K ∉ (K0 : Set ReductionData), deltaP q K ≤ C / (q : ℝ≥0∞) ^ 2 :=
  ⟨9, 2, by norm_num, fun q _ _ _ hK => deltaP_le_nine_div_sq q hK⟩

end WeierstrassCurve
