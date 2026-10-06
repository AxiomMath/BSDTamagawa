/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.Family.ReductionDecomposition
public import BSDTamagawa.LocalDensity.K0Mass

/-!
# The additive reduction mass

For a prime `p ≥ 5` and `n ≥ 1`, Griffin–Ono–Tsai state the asymptotic

  `δ_p(I_n^sp) = δ_p(I_n^ns) = (p-1)/(2p^{n+1}) + O(p^{-n-2})`

for the split and non-split multiplicative strata, together with the bound
`∑_{K additive} δ_p(K) = O(p^{-2})` for the additive Kodaira types. This file proves the additive
bound, with the explicit constant `9` and at every prime.

## Main definitions

* `WeierstrassCurve.additiveMass`: the total mass `∑_{K additive} δ_p(K)`.

## Main results

* `WeierstrassCurve.additiveMass_le_nine_div_sq`: `∑_{K additive} δ_p(K) ≤ 9/p²` at every prime.
* `WeierstrassCurve.exists_additive_mass_bound`: the same bound in `O(p^{-2})` form.

## References

* M. Griffin, K. Ono, W.-L. Tsai, *Tamagawa products of elliptic curves over `ℚ`*, Quart. J. Math.
  72 (2021), Table 5.
-/

@[expose] public section

namespace WeierstrassCurve

open scoped ENNReal
open BSDTamagawa.LocalReduction

/-! ### The additive locus -/

/-- Every additive reduction datum lies outside `𝒦₀ = {(I_0, 1), (I_1, 1)}`. -/
theorem kAdd_subset_compl_K0 :
    (kAdd : Set ReductionData) ⊆ (K0ᶜ : Set ReductionData) := by
  intro K hK hmem
  rw [mem_kAdd_iff] at hK
  simp only [K0, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h <;> rw [h] at hK <;> simp at hK

variable (p : ℕ) [Fact p.Prime]

/-- The total additive mass `∑_{K ∈ 𝒦_add} δ_p(K)`, where `𝒦_add = {K | κ(K).reduction = Additive}`
is the set of reduction data of additive type. -/
noncomputable def additiveMass : ℝ≥0∞ := ∑' K : ↥(kAdd : Set ReductionData), deltaP p K

/-- `∑_{K additive} δ_p(K) ≤ 9/p²` at every prime `p`. -/
theorem additiveMass_le_nine_div_sq : additiveMass p ≤ 9 / (p : ℝ≥0∞) ^ 2 :=
  (ENNReal.tsum_mono_subtype (deltaP p) kAdd_subset_compl_K0).trans
    (tsum_compl_K0_le_nine_div_sq p)

/-- There is `C > 0` with `∑_{K additive} δ_q(K) ≤ C/q²` at every prime `q`. -/
@[bsd_tamagawa "T020b"]
theorem exists_additive_mass_bound :
    ∃ C : ℝ≥0∞, 0 < C ∧ ∀ (q : ℕ) [Fact q.Prime], additiveMass q ≤ C / (q : ℝ≥0∞) ^ 2 :=
  ⟨9, by norm_num, fun q _ => additiveMass_le_nine_div_sq q⟩

end WeierstrassCurve
