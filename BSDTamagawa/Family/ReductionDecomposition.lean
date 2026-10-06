/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.EllipticCurve.Tate.Defs

/-!
# The decomposition `𝒦 = 𝒦_good ∪ 𝒦_mult ∪ 𝒦_add`

The set `𝒦 = KodairaSymbol × ℕ` of local reduction data splits, disjointly and exhaustively, into
the good, multiplicative and additive strata, cut out by the underlying Kodaira symbol `κ(K) = K.1`
through `WeierstrassCurve.KodairaSymbol.reduction`: `κ(𝒦_good) = {I₀}`, `κ(𝒦_mult) = {Iₙ : n ≥ 1}`
and `κ(𝒦_add) = {II, III, IV, I₀*, Iₙ* (n ≥ 1), IV*, III*, II*}`.

## Main definitions

* `WeierstrassCurve.kGood`, `WeierstrassCurve.kMult`, `WeierstrassCurve.kAdd`: the three strata.

## Main results

* `WeierstrassCurve.mem_kGood_iff`, `WeierstrassCurve.mem_kMult_iff`,
  `WeierstrassCurve.mem_kAdd_iff`: the Kodaira symbols of each stratum.
* `WeierstrassCurve.kGood_union_kMult_union_kAdd`: the strata cover `𝒦`.
* `WeierstrassCurve.disjoint_kGood_kMult`, `WeierstrassCurve.disjoint_kGood_kAdd`,
  `WeierstrassCurve.disjoint_kMult_kAdd`: the strata are pairwise disjoint.

## Implementation notes

The split/non-split labels `Iₙ^sp`, `Iₙ^ns` share the underlying symbol `Iₙ`, which is all the pair
encoding of `𝒦` records; the second component of a datum is unconstrained in every stratum.
-/

@[expose] public section

namespace WeierstrassCurve

/-- The good-reduction stratum `𝒦_good`: the local reduction data
`K = (Kodaira symbol, component-group order)` whose Kodaira symbol `κ(K)` has good reduction. -/
@[bsd_tamagawa "T007"]
def kGood : Set (KodairaSymbol × ℕ) := {K | K.1.reduction = Reduction.Good}

/-- The multiplicative stratum `𝒦_mult`: the local reduction data whose Kodaira symbol `κ(K)` has
multiplicative reduction. -/
@[bsd_tamagawa "T007"]
def kMult : Set (KodairaSymbol × ℕ) := {K | K.1.reduction = Reduction.Multiplicative}

/-- The additive stratum `𝒦_add`: the local reduction data whose Kodaira symbol `κ(K)` has additive
reduction. -/
@[bsd_tamagawa "T007"]
def kAdd : Set (KodairaSymbol × ℕ) := {K | K.1.reduction = Reduction.Additive}

/-- `κ(𝒦_good) = {I₀}`: a datum lies in the good-reduction stratum exactly when its Kodaira symbol
is `I₀`. -/
@[simp, bsd_tamagawa "T007"]
lemma mem_kGood_iff {K : KodairaSymbol × ℕ} : K ∈ kGood ↔ K.1 = KodairaSymbol.I 0 := by
  cases hk : K.1 <;> simp [kGood, KodairaSymbol.reduction, hk]

/-- `κ(𝒦_mult) = {Iₙ : n ≥ 1}`: a datum lies in the multiplicative stratum exactly when its Kodaira
symbol is `Iₙ` for some `n ≥ 1`. -/
@[bsd_tamagawa "T007"]
lemma mem_kMult_iff {K : KodairaSymbol × ℕ} :
    K ∈ kMult ↔ ∃ n : ℕ, 1 ≤ n ∧ K.1 = KodairaSymbol.I n := by
  cases hk : K.1 <;> simp [kMult, KodairaSymbol.reduction, hk, Nat.one_le_iff_ne_zero]

/-- `κ(𝒦_add) = {II, III, IV, I₀*, Iₙ* (n ≥ 1), IV*, III*, II*}`: a datum lies in the additive
stratum exactly when its Kodaira symbol is one of these, the starred family `Iₙ*` being taken over
all `n ≥ 0`. -/
@[bsd_tamagawa "T007"]
lemma mem_kAdd_iff {K : KodairaSymbol × ℕ} :
    K ∈ kAdd ↔ K.1 = KodairaSymbol.II ∨ K.1 = KodairaSymbol.III ∨
      K.1 = KodairaSymbol.IV ∨ (∃ n : ℕ, K.1 = KodairaSymbol.I! n) ∨
      K.1 = KodairaSymbol.IV! ∨ K.1 = KodairaSymbol.III! ∨ K.1 = KodairaSymbol.II! := by
  cases hk : K.1 <;> simp [kAdd, KodairaSymbol.reduction, hk, ite_eq_iff]

/-- `𝒦 = 𝒦_good ∪ 𝒦_mult ∪ 𝒦_add`: every local reduction datum lies in one of the three strata. -/
@[bsd_tamagawa "T007"]
lemma kGood_union_kMult_union_kAdd : kGood ∪ kMult ∪ kAdd = Set.univ := by
  ext K
  cases h : K.1.reduction <;> simp [kGood, kMult, kAdd, h]

/-- The strata `𝒦_good` and `𝒦_mult` are disjoint. -/
@[bsd_tamagawa "T007"]
lemma disjoint_kGood_kMult : Disjoint kGood kMult :=
  Set.disjoint_left.mpr fun _ hg hm => Reduction.noConfusion (hg.symm.trans hm)

/-- The strata `𝒦_good` and `𝒦_add` are disjoint. -/
@[bsd_tamagawa "T007"]
lemma disjoint_kGood_kAdd : Disjoint kGood kAdd :=
  Set.disjoint_left.mpr fun _ hg ha => Reduction.noConfusion (hg.symm.trans ha)

/-- The strata `𝒦_mult` and `𝒦_add` are disjoint. -/
@[bsd_tamagawa "T007"]
lemma disjoint_kMult_kAdd : Disjoint kMult kAdd :=
  Set.disjoint_left.mpr fun _ hm ha => Reduction.noConfusion (hm.symm.trans ha)

end WeierstrassCurve
