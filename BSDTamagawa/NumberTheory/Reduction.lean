/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.TatePositivity

/-!
# Positivity of the Tamagawa number of the local reduction map

The local reduction map `τ_p` sends a short Weierstrass model to the output of Tate's algorithm,
which records the Kodaira symbol together with the Tamagawa number. This file shows that the
Tamagawa number of `τ_p` is always positive, both on integer pairs `(a₄, a₆)` (`tauZ`) and on the
elliptic locus of the `p`-adic Haar space (`tauP`). In particular the fibre of the Tamagawa number
over `0` is empty, so the local density `δ_p(0)` vanishes.

## Main results

* `tauZ_tamagawaNumber_pos`: `0 < (tauZ p a₄ a₆).tamagawaNumber` for all integers `a₄`, `a₆`.
* `tauP_tamagawaNumber_pos`: `0 < (tauP p W).tamagawaNumber` for every elliptic short model `W`
  over `ℤ_p`.
-/

@[expose] public section

namespace WeierstrassCurve

/-- For all integers `a₄` and `a₆`, the Tamagawa number of the reduction datum `τ_p(a₄, a₆)` is
positive. On the singular locus `τ_p` takes the good-reduction value `(I₀, 1)`. -/
lemma tauZ_tamagawaNumber_pos (p : ℕ) [Fact p.Prime] (a₄ a₆ : ℤ) :
    0 < (tauZ p a₄ a₆).tamagawaNumber := by
  rw [tauZ]
  split
  · exact TateAlgorithm.run_tamagawaNumber_pos ..
  · exact Nat.one_pos

variable (p : ℕ) [Fact p.Prime]

/-- For every short Weierstrass model `W` over `ℤ_p` with `Δ ≠ 0`, the Tamagawa number of the
reduction datum `τ_p(W)` is positive. -/
lemma tauP_tamagawaNumber_pos (W : ShortNF.Elliptic ℤ_[p]) :
    0 < (tauP p W).tamagawaNumber :=
  TateAlgorithm.run_tamagawaNumber_pos ..

end WeierstrassCurve
