/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Defs

/-!
# The multi-index monomial `z^j`

For a tuple `j = (j_ℓ)_{ℓ ∈ P}` of nonnegative integers and `z ∈ ℂ^P`, the monomial is
`z^j := ∏_{ℓ ∈ P} z_ℓ ^ j_ℓ`. The definition, `BSDTamagawa.MultiIndex.multiMonomial`, lives in
`BSDTamagawa.Defs`; the exponent is a plain function `j : P → ℕ` on a finite type `P`.

## Main results

* `BSDTamagawa.MultiIndex.multiMonomial_zero`: the zero multi-index gives `1`.
-/

@[expose] public section

namespace BSDTamagawa.MultiIndex

open BSDTamagawa.PrimeParam

variable {P : Type*} [Fintype P]

/-- The zero multi-index gives `1`. -/
@[simp]
theorem multiMonomial_zero (z : ParamSpace P) : multiMonomial (fun _ => 0) z = 1 := by
  simp [multiMonomial]

end BSDTamagawa.MultiIndex
