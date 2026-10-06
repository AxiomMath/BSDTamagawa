/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.GOTTable.HasGOTDensitiesAll
public import BSDTamagawa.GOTTable.InStarColumnClose

/-!
# The Griffin–Ono–Tsai table of local Tamagawa densities

For every prime `p` and every `c`, the proportion `δ_p(c)` of short Weierstrass models over `ℤ_p`
whose `p`-minimal model has Tamagawa number `c` is given by the closed form `gotδ p c` of
Griffin–Ono–Tsai: the head values at `p = 2` (`gotHeadTwo`), at `p = 3` (`gotHeadThree`), the four
closed forms at `p ≥ 5` (`gotHeadLarge`), and in every case the geometric tail `α_p p^{-c}` for
`c ≥ 5` (`gotα`).

## Main results

* `WeierstrassCurve.hasGOTDensities`: `HasGOTDensities p` at every prime.
* `WeierstrassCurve.δ_eq_ofReal_gotδ`: `δ_p(t) = gotδ p t` for every prime and every `t`.

## Implementation notes

The table is Lemma 3.1 of Griffin–Ono–Tsai with two corrections; as printed it is false.

Lemma 3.1(3) prints, for `c = 4`,

  `δ_p(4) = p³(3p² − 2p − 1) / (6(p+1)(p⁸ + p⁶ + p⁴ + p² + 1))`.

The numerator is off by a sign, and `gotHeadLarge` uses `3p² − 2p + 1`. With the printed `− 1` the
column sums to `1 − p³ / (3(p+1)(p⁸ + p⁶ + p⁴ + p² + 1))`, short of `1` (by `125/7324218` at
`p = 5`); the two numerators differ by `2`, so the `δ_p(4)` terms differ by exactly the missing
mass. With `+ 1` the column sums to `1`.

Part (1), at `p = 2`, is correct as printed. In part (2), three of the four `p = 3` heads are
wrong: the printed column `(1924625/2125728, 510641/6377184, 7594/597861, 1193/652212)` must be
read as `(1924841/2125728, 509345/6377184, 30619/2391444, 1193/652212)`, a shift of
`(+3, −6, +3, 0)/29524`. The shift sums to zero, so the head total is unchanged. The error lies in
the cell `a₄ ≡ 54 (mod 81)`, `a₆ ≡ 27, 108, 135, 216 (mod 243)` of mass `4·3⁻⁹`, which is of type
`IV*` with `c = 3` at `a₆ ≡ 27, 135` and `c = 1` at `a₆ ≡ 108, 216`, while the printed column
counts it as `III*` with `c = 2`.

## References

* M. Griffin, K. Ono and W.-L. Tsai, *Tamagawa products of elliptic curves over `ℚ`*, Quart. J.
  Math. **72** (2021), no. 4, 1517–1543, `doi:10.1093/qmath/haab042`, Lemma 3.1.
-/

@[expose] public section

namespace WeierstrassCurve

/-- **The Griffin–Ono–Tsai table holds at every prime**: `HasGOTDensities p` for every prime
`p`. -/
theorem hasGOTDensities (p : ℕ) [Fact p.Prime] : HasGOTDensities p :=
  hasGOTDensities_of_large (fun _ _ hq => hasGOTDensities_of_five_le hq) p

/-- The local Tamagawa densities have the Griffin–Ono–Tsai closed forms at every prime and every
Tamagawa value: `δ_p(t) = gotδ p t`, the three columns of Lemma 3.1 of Griffin–Ono–Tsai with the
corrected `c = 4` numerator and the corrected `p = 3` head values. -/
@[bsd_tamagawa "T018"]
theorem δ_eq_ofReal_gotδ (p : ℕ) [Fact p.Prime] (t : ℕ) :
    δ p t = ENNReal.ofReal (gotδ p t) :=
  hasGOTDensities p t

end WeierstrassCurve
