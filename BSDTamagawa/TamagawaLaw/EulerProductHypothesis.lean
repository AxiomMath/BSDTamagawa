/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.TamagawaLaw.DirichletSeries

/-!
# The Euler product of the Tamagawa law off the half-plane, as a predicate

The local Euler factor of the limiting Tamagawa law at a prime `p` is
`L_p(s) = ∑_{t ≥ 1} δ_p(t) t^{-s}`. This file defines the assertion that, at a given `s : ℂ` at
which the Euler product `∏_{p ∈ 𝒫} L_p(s)` converges absolutely (that is, `∑_p ‖L_p(s) - 1‖ < ∞`),
the Dirichlet series `∑_{m ≥ 1} P_Tam(m) m^{-s}` converges absolutely and

`∑_{m ≥ 1} P_Tam(m) m^{-s} = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{-s})`,

and the same assertion at every `s : ℂ`.

## Main definitions

* `WeierstrassCurve.tamagawaEulerFactor`: the local factor `L_p(s)`.
* `WeierstrassCurve.HasEulerProductAt`: the assertion at a single `s : ℂ`.
* `WeierstrassCurve.HasEulerProductOffHalfPlane`: the assertion at every `s : ℂ`.

## References

* M. Griffin, K. Ono, W.-L. Tsai, *Tamagawa products of elliptic curves over `ℚ`*,
  Quart. J. Math. 72 (2021), Lemma 3.1.
-/

@[expose] public section

namespace WeierstrassCurve

/-- The Euler local factor `∑_{t ≥ 1} δ_p(t) t^{-s}` of the limiting Tamagawa law at the prime `p`
and the complex exponent `s`, the sum being written over all of `ℕ` (the term at `t = 0` vanishes).
-/
noncomputable def tamagawaEulerFactor (p : {q : ℕ // q.Prime}) (s : ℂ) : ℂ :=
  ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * (t : ℂ) ^ (-s)

/-- `tamagawaEulerFactor p s` is the series `∑_{t ≥ 0} δ_p(t) t^{-s}`. -/
theorem tamagawaEulerFactor_def (p : {q : ℕ // q.Prime}) (s : ℂ) :
    tamagawaEulerFactor p s
      = ∑' t : ℕ, ((@δ (p : ℕ) ⟨p.2⟩ t).toReal : ℂ) * (t : ℂ) ^ (-s) :=
  rfl

/-- The Euler product identity at a single `s : ℂ`: if the Euler product
`∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{-s})` converges absolutely at `s`, i.e.
`∑_p ‖(∑_t δ_p(t) t^{-s}) - 1‖ < ∞`, then the Dirichlet series `∑_{m ≥ 1} P_Tam(m) m^{-s}`
converges absolutely and equals that product. -/
def HasEulerProductAt (s : ℂ) : Prop :=
  Summable (fun p : {q : ℕ // q.Prime} => ‖tamagawaEulerFactor p s - 1‖) →
    (Summable fun m : ℕ => ‖(tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)‖) ∧
      ∑' m : ℕ, (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)
        = ∏' p : {q : ℕ // q.Prime}, tamagawaEulerFactor p s

/-- The Euler product identity `HasEulerProductAt s` at every `s : ℂ`, with no restriction on
`Re(s)`. -/
def HasEulerProductOffHalfPlane : Prop := ∀ s : ℂ, HasEulerProductAt s

end WeierstrassCurve
