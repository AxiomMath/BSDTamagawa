/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import BSDTamagawa.Defs

/-!
# The reduction type of a Kodaira symbol

The basic reduction type `WeierstrassCurve.Reduction` of the special fiber of a Weierstrass curve,
and the reduction type of a Kodaira symbol.
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R] {ϖ : R} {W : WeierstrassCurve R}

namespace WeierstrassCurve

/-- The basic reduction type of the special fiber `C` of a Weierstrass curve. -/
inductive Reduction
  /-- Good/stable reduction: `C` is non-singular. -/
  | Good
  /-- Multiplicative/semistable reduction: `C` has a node. -/
  | Multiplicative
  /-- Additive/unstable reduction: `C` has a cusp. -/
  | Additive

/-- The basic reduction type of the special fiber of a Weierstrass curve. -/
def KodairaSymbol.reduction : KodairaSymbol → Reduction
  | .I n => if n = 0 then .Good else .Multiplicative
  | _ => .Additive

end WeierstrassCurve
