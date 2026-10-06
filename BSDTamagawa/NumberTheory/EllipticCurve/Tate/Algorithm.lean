/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Sidharth Hariharan
-/
module

public import BSDTamagawa.NumberTheory.EllipticCurve.Tate.Defs

/-!
# The invariants Tate's algorithm computes

The invariants of a Weierstrass curve read off the output of Tate's algorithm
`WeierstrassCurve.TateAlgorithm.run`: the Kodaira symbol and the basic reduction type of the
special fiber, and the Tamagawa number.
-/

@[expose] public section

universe u

open Ideal

variable {R : Type u} [CommRing R] {ϖ : R} [span {ϖ} |>.IsMaximal] [PerfectField <| R ⧸ span {ϖ}]
  {W : WeierstrassCurve R} (hϖ : ϖ ≠ 0) (hΔ : W.Δ ≠ 0)

variable [IsNoetherianRing R] [IsDomain R]

namespace WeierstrassCurve.TateAlgorithm

/-- The Kodaira–Néron reduction type of the special fiber of a Weierstrass curve. -/
noncomputable def kodairaSymbol : KodairaSymbol := run hϖ hΔ |>.kodairaSymbol

/-- The basic reduction type of the special fiber of a Weierstrass curve. -/
noncomputable def reduction : Reduction := run hϖ hΔ |>.kodairaSymbol.reduction

/-- The Tamagawa number of a Weierstrass curve, which is equal to the number of components of its
special fiber which have multiplicity one and are defined over the residue field. -/
noncomputable def tamagawaNumber : ℕ := run hϖ hΔ |>.tamagawaNumber

end WeierstrassCurve.TateAlgorithm
