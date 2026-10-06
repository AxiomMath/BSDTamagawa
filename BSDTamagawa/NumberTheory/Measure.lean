/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import BSDTamagawa.Defs

/-!
# The measure space of short Weierstrass models

The space `WeierstrassCurve.ShortNF R` of short models `y² = x³ + a₄ x + a₆` over `R` carries the
measurable structure pulled back along `W ↦ (a₄, a₆)` and the pushforward of `volume` on `R × R`;
it splits into the singular locus `Δ = 0` and the elliptic locus `Δ ≠ 0`. This file proves that
the coefficients and the discriminant are measurable, and that over a domain with `2 ≠ 0` whose
volume has null singletons the singular locus is null, so that the elliptic locus has full
measure. For each fixed `a₆` the fibre `{a₄ | Δ = 0}` is the root set of a nonzero cubic, hence
finite. The base ring `ℤ_[p]`, with its normalized Haar measure, is one instance.

## Main results

* `WeierstrassCurve.ShortNF.Singular.finite_fiber`: for fixed `a₆`, only finitely many `a₄` give a
  singular model.
* `WeierstrassCurve.ShortNF.Singular.volume_eq`: the singular locus is null.
* `WeierstrassCurve.ShortNF.Elliptic.volume_eq`: the elliptic locus has full measure, so `μ_p`
  is a probability measure.
-/

@[expose] public section

open Ideal MeasureTheory Measure

attribute [local irreducible] MeasureTheory.Measure.addHaarMeasure

variable {R : Type*} {p : ℕ} [Fact p.Prime]

namespace PadicInt

/-- In `ℤ_[p]`, `2 ≠ 0`. -/
instance : Fact <| (2 : ℤ_[p]) ≠ 0 := ⟨OfNat.ofNat_ne_zero 2⟩

/-- The volume on `ℤ_[p]` is a probability measure. -/
instance : IsProbabilityMeasure <| @volume ℤ_[p] _ := ⟨addHaarMeasure_self⟩

/-- The volume on `ℤ_[p]` is an additive Haar measure. -/
instance : @volume ℤ_[p] _ |>.IsAddHaarMeasure := isAddHaarMeasure_addHaarMeasure _

/-- The point `0` is not isolated in `ℤ_[p]`: the punctured neighbourhood filter of `0` is
nontrivial. -/
instance : nhdsWithin (0 : ℤ_[p]) {0}ᶜ |>.NeBot :=
  Filter.neBot_iff.mpr fun h ↦ Infinite.of_injective _ Nat.cast_injective |>.not_finite <|
    @finite_of_compact_of_discrete _ _ _ <|
      discreteTopology_iff_isOpen_singleton_zero.mpr <|
        isOpen_singleton_iff_punctured_nhds _ |>.mpr h

end PadicInt

variable [CommRing R]

namespace WeierstrassCurve

namespace ShortNF

/-- The coefficient `a₁` is measurable on `ShortNF R`. -/
@[fun_prop] lemma measurable_a₁ [MeasurableSpace R] : Measurable fun W : ShortNF R ↦ W.val.a₁ :=
  measurable_const' fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp

/-- The coefficient `a₂` is measurable on `ShortNF R`. -/
@[fun_prop] lemma measurable_a₂ [MeasurableSpace R] : Measurable fun W : ShortNF R ↦ W.val.a₂ :=
  measurable_const' fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp

/-- The coefficient `a₃` is measurable on `ShortNF R`. -/
@[fun_prop] lemma measurable_a₃ [MeasurableSpace R] : Measurable fun W : ShortNF R ↦ W.val.a₃ :=
  measurable_const' fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp

/-- The coefficient `a₄` is measurable on `ShortNF R`. -/
@[fun_prop] lemma measurable_a₄ [MeasurableSpace R] : Measurable fun W : ShortNF R ↦ W.val.a₄ :=
  measurable_fst.comp <| comap_measurable _

/-- The coefficient `a₆` is measurable on `ShortNF R`. -/
@[fun_prop] lemma measurable_a₆ [MeasurableSpace R] : Measurable fun W : ShortNF R ↦ W.val.a₆ :=
  measurable_snd.comp <| comap_measurable _

/-- The quantity `b₂` is measurable on `ShortNF R`. -/
@[fun_prop] lemma measurable_b₂ [MeasurableSpace R] [MeasurableAdd₂ R] [MeasurableMul₂ R] :
    Measurable fun W : ShortNF R ↦ W.val.b₂ := by simp_rw [b₂]; fun_prop

/-- The quantity `b₄` is measurable on `ShortNF R`. -/
@[fun_prop] lemma measurable_b₄ [MeasurableSpace R] [MeasurableAdd₂ R] [MeasurableMul₂ R] :
    Measurable fun W : ShortNF R ↦ W.val.b₄ := by simp_rw [b₄]; fun_prop

/-- The quantity `b₆` is measurable on `ShortNF R`. -/
@[fun_prop] lemma measurable_b₆ [MeasurableSpace R] [MeasurableAdd₂ R] [MeasurableMul₂ R] :
    Measurable fun W : ShortNF R ↦ W.val.b₆ := by simp_rw [b₆]; fun_prop

/-- The quantity `b₈` is measurable on `ShortNF R`. -/
@[fun_prop] lemma measurable_b₈ [MeasurableSpace R] [MeasurableAdd₂ R] [MeasurableSub₂ R]
    [MeasurableMul₂ R] : Measurable fun W : ShortNF R ↦ W.val.b₈ := by simp_rw [b₈]; fun_prop

/-- The quantity `c₄` is measurable on `ShortNF R`. -/
@[fun_prop] lemma measurable_c₄ [MeasurableSpace R] [MeasurableAdd₂ R] [MeasurableSub₂ R]
    [MeasurableMul₂ R] : Measurable fun W : ShortNF R ↦ W.val.c₄ := by simp_rw [c₄]; fun_prop

/-- The quantity `c₆` is measurable on `ShortNF R`. -/
@[fun_prop] lemma measurable_c₆ [MeasurableSpace R] [MeasurableNeg R] [MeasurableAdd₂ R]
    [MeasurableMul₂ R] : Measurable fun W : ShortNF R ↦ W.val.c₆ := by simp_rw [c₆]; fun_prop

/-- The discriminant `Δ` is measurable on `ShortNF R`. -/
@[fun_prop] lemma measurable_Δ [MeasurableSpace R] [MeasurableNeg R] [MeasurableAdd₂ R]
    [MeasurableMul₂ R] : Measurable fun W : ShortNF R ↦ W.val.Δ := by simp_rw [Δ]; fun_prop

/-- The map `(a₄, a₆) ↦ ofProd a₄ a₆` from `R × R` to `ShortNF R` is measurable. -/
lemma measurable_ofProd [MeasurableSpace R] : Measurable (@ofProd R).uncurry :=
  measurable_comap_iff.mpr <| by fun_prop

/-- If the volume on `R` is a probability measure, so is the volume on `ShortNF R`. -/
instance [MeasureSpace R] [IsProbabilityMeasure <| @volume R _] :
    IsProbabilityMeasure <| @volume (ShortNF R) _ :=
  ⟨map_apply measurable_ofProd .univ |>.trans measure_univ⟩

namespace Singular

/-- The singular locus is measurable. -/
lemma measurableSet [MeasurableSpace R] [MeasurableNeg R] [MeasurableAdd₂ R] [MeasurableMul₂ R]
    [MeasurableSingletonClass R] : MeasurableSet <| Singular R :=
  measurable_Δ.eq_const 0 |>.setOf

open Polynomial in
/-- Over a domain with `2 ≠ 0`, for each fixed `a₆` only finitely many `a₄` make
`y² = x³ + a₄ x + a₆` singular. -/
lemma finite_fiber [Fact <| (2 : R) ≠ 0] [IsDomain R] (a₆ : R) :
    {a₄ : R | ofProd a₄ a₆ ∈ Singular R}.Finite :=
  rootSet_finite (-Cubic.toPoly ⟨2 ^ 6, 0, 0, 432 * a₆ ^ 2⟩) R |>.subset fun a₄ h ↦
    mem_rootSet.mpr ⟨neg_ne_zero.mpr <| Cubic.ne_zero_of_a_ne_zero <| pow_ne_zero _ Fact.out, by
      simp [Cubic.toPoly]; grind [b₂, b₄, b₆, b₈, Δ]⟩

/-- Over a domain `R` with `2 ≠ 0` whose volume is s-finite with null singletons, the singular
locus `{W | W.Δ = 0}` of short Weierstrass models has volume zero. -/
@[bsd_tamagawa "T032"]
lemma volume_eq [Fact <| (2 : R) ≠ 0] [IsDomain R] [MeasureSpace R]
    [NullSingletonClass <| @volume R _] [SFinite <| @volume R _] [MeasurableNeg R]
    [MeasurableAdd₂ R] [MeasurableMul₂ R] [MeasurableSingletonClass R] :
    volume (Singular R) = 0 :=
  map_apply measurable_ofProd measurableSet |>.trans <| by
    rw [volume_eq_prod, prod_apply_symm <| measurableSet.preimage measurable_ofProd]
    exact lintegral_eq_zero_of_ae_eq_zero <| .of_forall (finite_fiber · |>.measure_zero volume)

end Singular

namespace Elliptic

/-- The elliptic locus is measurable. -/
lemma measurableSet [MeasurableSpace R] [MeasurableNeg R] [MeasurableAdd₂ R] [MeasurableMul₂ R]
    [MeasurableSingletonClass R] : MeasurableSet <| Elliptic R :=
  Singular.measurableSet.compl

/-- Over a domain `R` with `2 ≠ 0` whose volume is a probability measure with null singletons,
the elliptic locus of `ShortNF R` has volume one. -/
lemma volume_eq [Fact <| (2 : R) ≠ 0] [IsDomain R] [MeasureSpace R]
    [NullSingletonClass <| @volume R _] [IsProbabilityMeasure <| @volume R _] [MeasurableNeg R]
    [MeasurableAdd₂ R] [MeasurableMul₂ R] [MeasurableSingletonClass R] :
    volume (Elliptic R) = 1 :=
  prob_compl_eq_one_iff Singular.measurableSet |>.mpr Singular.volume_eq

/-- Under the hypotheses of `volume_eq`, the measure `μ_p` on `Elliptic R` is a probability
measure. -/
instance [Fact <| (2 : R) ≠ 0] [IsDomain R] [MeasureSpace R] [NullSingletonClass <| @volume R _]
    [IsProbabilityMeasure <| @volume R _] [MeasurableNeg R] [MeasurableAdd₂ R] [MeasurableMul₂ R]
    [MeasurableSingletonClass R] : IsProbabilityMeasure <| @volume (Elliptic R) _ :=
  ⟨Subtype.volume_univ measurableSet.nullMeasurableSet |>.trans volume_eq⟩

end Elliptic

end ShortNF

end WeierstrassCurve
