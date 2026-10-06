/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.WildHeadCloseAtTwo
public import BSDTamagawa.GOTTable.HasGOTDensitiesThree

/-!
# The table at every prime, from its three columns

Every prime is `2`, `3`, or at least `5`. The Griffin–Ono–Tsai table holds at the two wild primes
by `hasGOTDensities_two` and `hasGOTDensities_three`; combined with the table at every prime
`q ≥ 5`, it therefore holds at every prime.

## Main results

* `WeierstrassCurve.hasGOTDensities_of_large`: if `HasGOTDensities q` holds for every prime
  `q ≥ 5`, then `HasGOTDensities p` holds for every prime `p`.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalConstancy

/-- If the Griffin–Ono–Tsai table holds at every prime `q ≥ 5`, then it holds at every prime
`p`. -/
theorem hasGOTDensities_of_large
    (hlarge : ∀ (q : ℕ) [Fact q.Prime], 5 ≤ q → HasGOTDensities q)
    (p : ℕ) [Fact p.Prime] : HasGOTDensities p := by
  rcases prime_eq_two_or_eq_three_or_five_le (Fact.out : p.Prime) with h | h | h
  · subst h; exact hasGOTDensities_two
  · subst h; exact hasGOTDensities_three
  · exact hlarge p h

end WeierstrassCurve

end
