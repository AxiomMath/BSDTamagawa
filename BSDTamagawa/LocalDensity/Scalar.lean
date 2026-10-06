/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.NumberTheory.Reduction

/-!
# The scalar local density at zero

`δ p t` is the proportion of short Weierstrass models over `ℤ_p` whose local Tamagawa number at `p`
equals `t`, i.e. the `μ_p`-measure of `{W : c(τ_p(W)) = t}`; it equals `∑_{K ∈ 𝒦, c(K) = t} δ_p(K)`
by countable additivity. Since Tate's algorithm never returns a zero Tamagawa number, the fibre
over `0` is empty and `δ_p(0) = 0`.

## Main results

* `WeierstrassCurve.δ_zero`: `δ_p(0) = 0`.
-/

@[expose] public section

open MeasureTheory

variable {p : ℕ} [Fact p.Prime]

namespace WeierstrassCurve

variable (p) in
/-- `δ_p(0) = 0`: a local Tamagawa number is never `0`, so the fibre `{W | c(τ_p(W)) = 0}` is
empty. -/
lemma δ_zero : δ p 0 = 0 := by
  have hempty : {W : ShortNF.Elliptic ℤ_[p] | (tauP p W).tamagawaNumber = 0} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun W hW => absurd hW (tauP_tamagawaNumber_pos p W).ne'
  rw [δ, hempty, measure_empty]

end WeierstrassCurve
