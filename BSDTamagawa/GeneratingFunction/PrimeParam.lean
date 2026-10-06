/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module


public import BSDTamagawa.Defs

/-!
# The prime-parameter space `ℂ^Π`

Throughout, `Π` is a fixed finite set, thought of as a finite set of (rational) primes (it is
allowed to be empty), and `ℓ, ℓ'` denote generic elements of `Π`. The arithmetic role of the
elements of `Π` is irrelevant here, so `Π` is modelled by an abstract type `P`. The parameter space
`ParamSpace P = ℂ^Π = ∏_{ℓ ∈ Π} ℂ` is defined in `BSDTamagawa.Defs`; its elements are the
prime-parameter vectors `z = (z_ℓ)_{ℓ ∈ Π}`.

## Main definitions

* `BSDTamagawa.PrimeParam.prL ℓ`: the coordinate projection `pr_ℓ`, `z ↦ z_ℓ`.
* `BSDTamagawa.PrimeParam.componentsEquiv`: the components map `Φ : ℂ^Π → ∏_{ℓ ∈ Π} ℂ`,
  `Φ z = (z ℓ)_{ℓ ∈ Π}`, as the identity `ℂ`-linear equivalence.
-/

@[expose] public section

namespace BSDTamagawa.PrimeParam

/-! ### Definitions -/

/-- **Coordinate projection `pr_ℓ`.** Sends a prime-parameter vector to its `ℓ`-th component
`z_ℓ = z ℓ`. -/
def prL {P : Type*} (ℓ : P) (z : ParamSpace P) : ℂ := z ℓ

/-- The projection `pr_ℓ` evaluates a vector at `ℓ`. -/
@[simp]
theorem prL_apply {P : Type*} (ℓ : P) (z : ParamSpace P) : prL ℓ z = z ℓ := rfl

/-- **Components map `Φ`.** Sends a prime-parameter vector to its indexed family of components. As
both source and target are `∏_{ℓ ∈ P} ℂ`, this is the identity `ℂ`-linear equivalence; packaging it
as a `LinearEquiv` records that it is a `ℂ`-linear bijection. -/
def componentsEquiv {P : Type*} : ParamSpace P ≃ₗ[ℂ] (P → ℂ) := LinearEquiv.refl ℂ (P → ℂ)

/-- The components map `Φ` sends a vector to itself. -/
@[simp]
theorem componentsEquiv_apply {P : Type*} (z : ParamSpace P) : componentsEquiv z = z := rfl

end BSDTamagawa.PrimeParam
