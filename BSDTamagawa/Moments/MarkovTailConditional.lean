/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.TamagawaLaw.TotalMass

/-!
# Summability of the tails of the limiting Tamagawa density

For every `M : ℕ` the tail family `n ↦ P_Tam(n + M)` of the limiting Tamagawa density `P_Tam` is
summable. This is the tail `∑_{m ≥ M} P_Tam(m)`, encoded as `∑' n : ℕ, P_Tam(n + M)`, that enters
the Markov bound `∑_{m ≥ M} P_Tam(m) ≤ M_k / M^{k}` for `M ≥ 1`, where `M_k` is the `k`th moment.

## Main results

* `WeierstrassCurve.summable_tamagawaDensity_shift`: the tail `n ↦ P_Tam(n + M)` is summable.
-/

@[expose] public section

namespace WeierstrassCurve

/-- For every `M : ℕ`, the tail family `n ↦ P_Tam(n + M)` is summable. -/
theorem summable_tamagawaDensity_shift (M : ℕ) :
    Summable fun n : ℕ => tamagawaDensity (n + M) :=
  (summable_nat_add_iff M).mpr summable_tamagawaDensity

end WeierstrassCurve
