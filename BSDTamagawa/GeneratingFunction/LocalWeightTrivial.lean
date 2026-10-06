/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.GeneratingFunction.MultiMonomial

/-!
# The local weight is trivial on `𝒦₀`

For every `K ∈ 𝒦₀ = {(I₀, 1), (I₁, 1)}` and every choice of parameters `(s, u, w, 𝐳, 𝐮)`, the local
weight satisfies `Φ(K; s, u, w, 𝐳, 𝐮) = 1`, provided `Λ` is disjoint from `𝒦₀`. Every member of
`𝒦₀` has local Tamagawa number `1`, which makes the first four factors of `Φ` equal to `1`, and
disjointness makes every exponent of the last factor `0`.

## Main results

* `WeierstrassCurve.localWeight_eq_one`: `Φ(K; s, u, w, 𝐳, 𝐮) = 1` for `K ∈ 𝒦₀`.

## Implementation notes

The hypothesis that `Λ` avoids `𝒦₀` is necessary: with `Λ = {(I₀, 1)}`, `K = (I₀, 1)` and
`u_{(I₀,1)} = 2` the last factor is `2`.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.MultiIndex

open scoped Classical in
/-- If `K ∈ 𝒦₀` and `Λ` avoids `𝒦₀`, then `Φ(K; s, u, w, 𝐳, 𝐮) = 1` for every choice of the
parameters `s, u, w : ℂ`, `𝐳 = (z_ℓ)_{ℓ ∈ Π}` and `𝐮 = (u_{K'})_{K' ∈ Λ}`. -/
@[bsd_tamagawa "T016"]
theorem localWeight_eq_one (Λ : Finset (KodairaSymbol × ℕ)) (P : Finset ℕ)
    {K : KodairaSymbol × ℕ} (hK : K ∈ K0) (hΛ : ∀ K' ∈ Λ, K' ∉ K0)
    (s u w : ℂ) (z : P → ℂ) (uΛ : Λ → ℂ) :
    localWeight Λ P K s u w z uΛ = 1 := by
  have hc : K.2 = 1 := by
    simp only [K0, Set.mem_insert_iff, Set.mem_singleton_iff] at hK
    obtain rfl | rfl := hK <;> rfl
  have hlast : (fun K' : Λ => if K = (K' : KodairaSymbol × ℕ) then 1 else 0) = fun _ => 0 := by
    funext K'
    refine ite_eq_right fun h => hΛ _ K'.2 ?_
    rw [← h]; exact hK
  rw [localWeight, hc, hlast, multiMonomial_zero]
  have hz : (fun ℓ : P => padicValNat ℓ 1) = fun _ => 0 :=
    funext fun ℓ => padicValNat_one_right ℓ
  rw [hz, multiMonomial_zero, ArithmeticFunction.cardFactors_one, Nat.cast_one,
    Complex.one_cpow]
  norm_num

end WeierstrassCurve
