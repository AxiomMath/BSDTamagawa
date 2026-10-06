/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.NumberTheory.HeadDensityFourExact

/-!
# The root-count classification of the depressed cubics over `𝔽_p`

For a prime `p ≥ 5`, the `p²` pairs `(A, B) ∈ 𝔽_p × 𝔽_p`, equivalently the depressed monic cubics
`X³ + AX + B`, are classified by the number of roots of the cubic in `𝔽_p`. Writing
`rₖ = |rootCountResidues p k|`, we prove the subtraction-free forms

  `3r₀ + 1 = p²`,  `2r₁ + p = p² + 2`,  `r₂ + 1 = p`,  `6r₃ + 3p = p² + 2`

of `r₀ = (p² - 1)/3`, `r₁ = p(p-1)/2 + 1`, `r₂ = p - 1` and `r₃ = (p-1)(p-2)/6`.

The proof rests on two incidence counts valid at every prime, `∑ #roots = p²` and
`∑ #roots·(#roots - 1) = p² - p`, together with the identification of the two-root class with the
cubics having a double but not a triple root. Among the `p² - p` separable cubics, the classes with
`3`, `1` and `0` roots are those of Galois orbit type `1+1+1`, `1+2` and `3`; we count the
separable one-root class, `p(p-1)/2`.

## Main definitions

* `WeierstrassCurve.cubicRootSet`: the roots in `𝔽_p` of `X³ + AX + B`.
* `WeierstrassCurve.rootCountResidues`: the pairs `(A, B)` whose cubic has exactly `k` roots.
* `WeierstrassCurve.oneRootResidues`: the separable pairs whose cubic has exactly one root.

## Main results

* `WeierstrassCurve.sum_card_cubicRootSet`: `∑_{(A,B)} #roots = p²`.
* `WeierstrassCurve.sum_card_offDiag_cubicRootSet`: `∑_{(A,B)} #roots·(#roots - 1) + p = p²`.
* `WeierstrassCurve.rootCountResidues_two_eq`: for `p ≥ 5`, a depressed cubic has exactly two roots
  if and only if it has a double but not a triple root.
* `WeierstrassCurve.card_rootCountResidues_zero`, `WeierstrassCurve.card_rootCountResidues_one`,
  `WeierstrassCurve.card_rootCountResidues_two`, `WeierstrassCurve.card_rootCountResidues_three`:
  the four counts above, for `p ≥ 5`.
* `WeierstrassCurve.card_oneRootResidues`: `2·|oneRootResidues p| + p = p²` for `p ≥ 5`.
-/

@[expose] public section

namespace WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-! ### The root set of a depressed cubic over `𝔽_p` -/

/-- **The roots in `𝔽_p` of the depressed monic cubic `X³ + AX + B`** attached to the pair
`(A, B) = c`. -/
def cubicRootSet (c : ZMod p × ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter fun x => x ^ 3 + c.1 * x + c.2 = 0

/-- `x` lies in `cubicRootSet c` exactly when `x ^ 3 + c.1 * x + c.2 = 0`. -/
theorem mem_cubicRootSet {c : ZMod p × ZMod p} {x : ZMod p} :
    x ∈ cubicRootSet c ↔ x ^ 3 + c.1 * x + c.2 = 0 := by
  simp only [cubicRootSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- `cubicRootSet` is the set of distinct polynomial roots of `Cubic.toPoly ⟨1, 0, A, B⟩`. -/
theorem cubicRootSet_eq_roots_toFinset (c : ZMod p × ZMod p) :
    cubicRootSet c = (Cubic.toPoly ⟨1, 0, c.1, c.2⟩ : Polynomial (ZMod p)).roots.toFinset := by
  have h0 : (Cubic.toPoly ⟨1, 0, c.1, c.2⟩ : Polynomial (ZMod p)) ≠ 0 :=
    Cubic.ne_zero_of_a_ne_zero (P := ⟨1, 0, c.1, c.2⟩) one_ne_zero
  have heval : ∀ x : ZMod p, (Cubic.toPoly ⟨1, 0, c.1, c.2⟩ : Polynomial (ZMod p)).eval x
      = x ^ 3 + c.1 * x + c.2 := by
    intro x
    simp only [Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  ext x
  rw [mem_cubicRootSet, Multiset.mem_toFinset, Polynomial.mem_roots']
  simp only [Polynomial.IsRoot, heval]
  exact ⟨fun h => ⟨h0, h⟩, fun h => h.2⟩

/-- A cubic has at most three distinct roots. -/
theorem card_cubicRootSet_le (c : ZMod p × ZMod p) : (cubicRootSet c).card ≤ 3 := by
  rw [cubicRootSet_eq_roots_toFinset]
  refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans (le_of_eq ?_))
  exact Cubic.natDegree_of_a_ne_zero (P := ⟨1, 0, c.1, c.2⟩) one_ne_zero

variable (p) in
/-- **The residue pairs `(A, B) ∈ 𝔽_p²` whose depressed cubic `X³ + AX + B` has exactly `k` roots
in `𝔽_p`.** Only `k ≤ 3` is ever nonempty (`card_cubicRootSet_le`). -/
def rootCountResidues (k : ℕ) : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun c => (cubicRootSet c).card = k

/-- A pair `c` lies in `rootCountResidues p k` exactly when its cubic has `k` roots in `𝔽_p`. -/
theorem mem_rootCountResidues {k : ℕ} {c : ZMod p × ZMod p} :
    c ∈ rootCountResidues p k ↔ (cubicRootSet c).card = k := by
  simp only [rootCountResidues, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The four classes `k = 0, 1, 2, 3` partition the plane, so their counts sum to `p²`. -/
theorem card_rootCountResidues_sum :
    (rootCountResidues p 0).card + (rootCountResidues p 1).card + (rootCountResidues p 2).card
      + (rootCountResidues p 3).card = p ^ 2 := by
  have hmaps : ∀ c ∈ (Finset.univ : Finset (ZMod p × ZMod p)),
      (cubicRootSet c).card ∈ Finset.range 4 :=
    fun c _ => Finset.mem_range.2 (Nat.lt_succ_of_le (card_cubicRootSet_le c))
  have hfib : ∀ k ∈ Finset.range 4,
      ((Finset.univ : Finset (ZMod p × ZMod p)).filter fun c => (cubicRootSet c).card = k).card
        = (rootCountResidues p k).card := fun k _ => by simp only [rootCountResidues]
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ, Fintype.card_prod, ZMod.card, ← sq, Finset.sum_congr rfl hfib] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  omega

/-! ### The first double count: `∑ #roots = p²` -/

/-- **The fibre of `(x, A) ↦ (A, -x³ - Ax)` over `(A, B)` is the root set of `X³ + AX + B`.** Given
a root `x` and the coefficient `A`, the coefficient `B` is forced. -/
theorem card_filter_incidenceParam (c : ZMod p × ZMod p) :
    ((Finset.univ : Finset (ZMod p × ZMod p)).filter
        fun q => (q.2, -q.1 ^ 3 - q.2 * q.1) = c).card = (cubicRootSet c).card := by
  have himg : ((Finset.univ : Finset (ZMod p × ZMod p)).filter
      fun q => (q.2, -q.1 ^ 3 - q.2 * q.1) = c) = (cubicRootSet c).image fun x => (x, c.1) := by
    ext q
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hq⟩
      obtain ⟨hA, hB⟩ := Prod.ext_iff.1 hq
      refine ⟨q.1, mem_cubicRootSet.2 ?_, ?_⟩
      · rw [← hA, ← hB]
        ring
      · rw [← hA]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨Finset.mem_univ _, Prod.ext_iff.2 ⟨rfl, ?_⟩⟩
      change -y ^ 3 - c.1 * y = c.2
      linear_combination -mem_cubicRootSet.1 hy
  rw [himg, Finset.card_image_of_injective _ (fun x y h => (Prod.ext_iff.1 h).1)]

/-- **(a) `∑_{(A,B)} #roots = p²`.** The incidence set `{((A,B), x) : x³ + Ax + B = 0}` is
parametrized bijectively by `(x, A)`, because `x` and `A` force `B = -x³ - Ax`. Holds at every
prime; no hypothesis `5 ≤ p`. -/
theorem sum_card_cubicRootSet : ∑ c : ZMod p × ZMod p, (cubicRootSet c).card = p ^ 2 := by
  have hmaps : ∀ q ∈ (Finset.univ : Finset (ZMod p × ZMod p)),
      (q.2, -q.1 ^ 3 - q.2 * q.1) ∈ (Finset.univ : Finset (ZMod p × ZMod p)) :=
    fun q _ => Finset.mem_univ _
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ, Fintype.card_prod, ZMod.card, ← sq,
    Finset.sum_congr rfl fun c _ => card_filter_incidenceParam c] at h
  exact h.symm

/-! ### The second double count: `∑ #roots·(#roots - 1) = p² - p` -/

/-- **The ordered pairs of distinct roots of a common depressed cubic, at a fixed `(A, B)`.** For
`x ≠ y` the two equations force `A = -(x² + xy + y²)` and then `B = x²y + xy²`, i.e.
`(A, B) = rootPairSym (x, y)`; conversely both members of a pair are roots of its own cubic. -/
theorem filter_offDiag_rootPairSym (c : ZMod p × ZMod p) :
    ((Finset.univ : Finset (ZMod p)).offDiag.filter fun q => rootPairSym q = c)
      = (cubicRootSet c).offDiag := by
  ext q
  obtain ⟨x, y⟩ := q
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and, mem_cubicRootSet]
  constructor
  · rintro ⟨hxy, rfl⟩
    exact ⟨(cubic_rootPairSym_eq_zero x y).1, (cubic_rootPairSym_eq_zero x y).2, hxy⟩
  · rintro ⟨hx, hy, hxy⟩
    have hA : (x - y) * (x ^ 2 + x * y + y ^ 2 + c.1) = 0 := by linear_combination hx - hy
    have h1 : x ^ 2 + x * y + y ^ 2 + c.1 = 0 :=
      (mul_eq_zero.1 hA).resolve_left (sub_ne_zero.2 hxy)
    refine ⟨hxy, Prod.ext ?_ ?_⟩
    · simp only [rootPairSym]
      linear_combination -h1
    · simp only [rootPairSym]
      linear_combination -hx + x * h1

/-- The off-diagonal of `𝔽_p` has `p² - p` points, stated additively. -/
theorem card_offDiag_univ_add : ((Finset.univ : Finset (ZMod p)).offDiag).card + p = p ^ 2 := by
  have hpp : p ≤ p * p := Nat.le_mul_self p
  rw [Finset.offDiag_card, Finset.card_univ, ZMod.card, pow_two]
  omega

/-- **(b) `∑_{(A,B)} #roots·(#roots - 1) = p² - p`**, stated additively so no truncated natural
subtraction occurs. Each of the `p(p-1)` ordered pairs `x ≠ y` of residues is a pair of distinct
roots of exactly one depressed cubic, namely `rootPairSym (x, y)`. Holds at every prime; no
hypothesis `5 ≤ p`. -/
theorem sum_card_offDiag_cubicRootSet :
    (∑ c : ZMod p × ZMod p, ((cubicRootSet c).offDiag).card) + p = p ^ 2 := by
  have hmaps : ∀ q ∈ (Finset.univ : Finset (ZMod p)).offDiag,
      rootPairSym q ∈ (Finset.univ : Finset (ZMod p × ZMod p)) := fun q _ => Finset.mem_univ _
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.sum_congr rfl fun c _ => congrArg Finset.card (filter_offDiag_rootPairSym c)] at h
  rw [← h]
  exact card_offDiag_univ_add

/-! ### The two double counts in terms of the four class sizes -/

/-- **(a) as `r₁ + 2r₂ + 3r₃ = p²`.** -/
theorem card_rootCountResidues_incidence :
    (rootCountResidues p 1).card + 2 * (rootCountResidues p 2).card
      + 3 * (rootCountResidues p 3).card = p ^ 2 := by
  have hmaps : ∀ c ∈ (Finset.univ : Finset (ZMod p × ZMod p)),
      (cubicRootSet c).card ∈ Finset.range 4 :=
    fun c _ => Finset.mem_range.2 (Nat.lt_succ_of_le (card_cubicRootSet_le c))
  have h := Finset.sum_fiberwise_of_maps_to hmaps fun c => (cubicRootSet c).card
  have hinner : ∀ k ∈ Finset.range 4,
      (∑ c ∈ (Finset.univ : Finset (ZMod p × ZMod p)).filter
          fun c => (cubicRootSet c).card = k, (cubicRootSet c).card)
        = (rootCountResidues p k).card * k := by
    intro k _
    rw [Finset.sum_congr rfl fun c hc => (Finset.mem_filter.1 hc).2, Finset.sum_const,
      smul_eq_mul]
    simp only [rootCountResidues]
  rw [Finset.sum_congr rfl hinner] at h
  have ha := sum_card_cubicRootSet (p := p)
  rw [← h] at ha
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero, mul_one] at ha
  omega

/-- **(b) as `2r₂ + 6r₃ + p = p²`.** -/
theorem card_rootCountResidues_offDiag :
    2 * (rootCountResidues p 2).card + 6 * (rootCountResidues p 3).card + p = p ^ 2 := by
  have hmaps : ∀ c ∈ (Finset.univ : Finset (ZMod p × ZMod p)),
      (cubicRootSet c).card ∈ Finset.range 4 :=
    fun c _ => Finset.mem_range.2 (Nat.lt_succ_of_le (card_cubicRootSet_le c))
  have h := Finset.sum_fiberwise_of_maps_to hmaps fun c => ((cubicRootSet c).offDiag).card
  have hinner : ∀ k ∈ Finset.range 4,
      (∑ c ∈ (Finset.univ : Finset (ZMod p × ZMod p)).filter
          fun c => (cubicRootSet c).card = k, ((cubicRootSet c).offDiag).card)
        = (rootCountResidues p k).card * (k * k - k) := by
    intro k _
    rw [Finset.sum_congr rfl fun c hc => by
      rw [Finset.offDiag_card, (Finset.mem_filter.1 hc).2], Finset.sum_const, smul_eq_mul]
    simp only [rootCountResidues]
  rw [Finset.sum_congr rfl hinner] at h
  have hb := sum_card_offDiag_cubicRootSet (p := p)
  rw [← h] at hb
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hb
  norm_num at hb
  omega

/-! ### The cuspidal cubic: where a repeated root lives, and how many roots it leaves -/

/-- **The root set of `X³ - 3s²X + 2s³ = (X - s)²(X + 2s)`** is `{s, -2s}`. -/
theorem cubicRootSet_cuspParam (s : ZMod p) : cubicRootSet (cuspParam s) = {s, -2 * s} := by
  ext x
  rw [mem_cubicRootSet]
  simp only [cuspParam, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hfac : (x - s) ^ 2 * (x - -2 * s) = 0 := by linear_combination h
    rcases mul_eq_zero.1 hfac with h' | h'
    · exact Or.inl (sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num : 2 ≠ 0)).1 h'))
    · exact Or.inr (by linear_combination h')
  · rintro (rfl | rfl) <;> ring

/-- The cusp `(0, 0)` is the pair whose cubic is `X³`; its only root is `0`. -/
theorem cubicRootSet_zero : cubicRootSet ((0, 0) : ZMod p × ZMod p) = {0} := by
  ext x
  rw [mem_cubicRootSet]
  simp only [Finset.mem_singleton]
  constructor
  · intro h
    exact (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).1 (by linear_combination h)
  · rintro rfl; ring

/-- **The dichotomy on the cuspidal cubic `4A³ + 27B² = 0` at `p ≥ 5`.** Such a pair is
`cuspParam s = (-3s², 2s³)`, its cubic is `(X - s)²(X + 2s)`, and so either `s = 0`, the pair is
the cusp `(0, 0)` and the cubic `X³` has the single root `0`; or `s ≠ 0`, the pair is not the cusp,
and the two roots `s ≠ -2s` are all of them. **This is where `5 ≤ p` is used**: `3` must be
invertible for `cuspidalResidues_eq_image` and for `s ≠ -2s`, and `2` for the former. -/
theorem card_cubicRootSet_of_mem_cuspidalResidues (hp : 5 ≤ p) {c : ZMod p × ZMod p}
    (hc : c ∈ cuspidalResidues p) :
    (c = (0, 0) ∧ (cubicRootSet c).card = 1) ∨ (c ≠ (0, 0) ∧ (cubicRootSet c).card = 2) := by
  have h3 : (3 : ZMod p) ≠ 0 := by
    simpa using natCast_ne_zero_of_lt (p := p) (n := 3) (by norm_num) (by omega)
  rw [cuspidalResidues_eq_image hp] at hc
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hc
  by_cases hs : s = 0
  · subst hs
    refine Or.inl ⟨by simp [cuspParam], ?_⟩
    rw [show (cuspParam (0 : ZMod p)) = (0, 0) from by simp [cuspParam], cubicRootSet_zero,
      Finset.card_singleton]
  · refine Or.inr ⟨?_, ?_⟩
    · intro h
      exact hs ((pow_eq_zero_iff (by norm_num : 2 ≠ 0)).1
        (by simpa using mul_left_cancel₀ (neg_ne_zero.2 h3) ((Prod.ext_iff.1 h).1.trans
          (by rw [mul_zero]) : -3 * s ^ 2 = -3 * 0)))
    · rw [cubicRootSet_cuspParam]
      refine Finset.card_pair fun h => hs ?_
      have h3s : (3 : ZMod p) * s = 0 := by linear_combination h
      exact (mul_eq_zero.1 h3s).resolve_left h3

/-- **A pair whose cubic has neither one nor two roots is separable**: the cuspidal cubic carries
only the one- and two-root classes (`card_cubicRootSet_of_mem_cuspidalResidues`). -/
theorem mem_ellipticResidues_of_card_ne (hp : 5 ≤ p) {c : ZMod p × ZMod p}
    (h1 : (cubicRootSet c).card ≠ 1) (h2 : (cubicRootSet c).card ≠ 2) :
    c ∈ ellipticResidues p := by
  simp only [ellipticResidues, Finset.mem_filter, Finset.mem_univ, true_and]
  intro h0
  have hc : c ∈ cuspidalResidues p := by
    simp only [cuspidalResidues, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h0
  rcases card_cubicRootSet_of_mem_cuspidalResidues hp hc with ⟨-, h⟩ | ⟨-, h⟩
  · exact h1 h
  · exact h2 h

/-! ### The four counts -/

/-- **`rootCountResidues p 2 = doubleRootResidues p`: exactly two roots is exactly a double but not
a triple root.** `⊆` is `Cubic.card_roots_ne_two` (a cubic with two distinct roots must have zero
discriminant) together with the observation that `A = 0` on the cuspidal cubic forces `B = 0`, the
cusp, whose cubic `X³` has one root. `⊇` is the cuspidal dichotomy. -/
theorem rootCountResidues_two_eq (hp : 5 ≤ p) :
    rootCountResidues p 2 = doubleRootResidues p := by
  have h3 : (3 : ZMod p) ≠ 0 := by
    simpa using natCast_ne_zero_of_lt (p := p) (n := 3) (by norm_num) (by omega)
  have h27 : (27 : ZMod p) ≠ 0 := fun h =>
    h3 ((pow_eq_zero_iff (by norm_num : 3 ≠ 0)).1
      (by linear_combination h))
  ext c
  rw [mem_rootCountResidues, doubleRootResidues, Finset.mem_filter, cuspidalResidues,
    Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro h
    have hdr : (⟨1, 0, c.1, c.2⟩ : Cubic (ZMod p)).HasDoubleRoot := by
      by_contra hnd
      exact Cubic.card_roots_ne_two (P := ⟨1, 0, c.1, c.2⟩) rfl hnd
        (by rw [← cubicRootSet_eq_roots_toFinset]; exact h)
    have h4 := (Cubic.hasDoubleRoot_depressed_iff c.1 c.2).1 hdr
    refine ⟨h4, fun hA => ?_⟩
    have hB : c.2 = 0 := by
      have h0 : (27 : ZMod p) * c.2 ^ 2 = 0 := by
        rw [hA] at h4
        linear_combination h4
      exact (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).1 ((mul_eq_zero.1 h0).resolve_left h27)
    rw [show c = ((0, 0) : ZMod p × ZMod p) from Prod.ext hA hB, cubicRootSet_zero,
      Finset.card_singleton] at h
    exact absurd h (by norm_num)
  · rintro ⟨h4, hA⟩
    have hc : c ∈ cuspidalResidues p := by simpa [cuspidalResidues] using h4
    rcases card_cubicRootSet_of_mem_cuspidalResidues hp hc with ⟨hcz, -⟩ | ⟨-, h⟩
    · exact absurd (by rw [hcz]) hA
    · exact h

/-- **`r₂ + 1 = p`**, i.e. `r₂ = p - 1`. -/
theorem card_rootCountResidues_two (hp : 5 ≤ p) : (rootCountResidues p 2).card + 1 = p := by
  rw [rootCountResidues_two_eq hp, card_doubleRootResidues hp]
  omega

/-- **`6r₃ + 3p = p² + 2`**, i.e. `r₃ = (p-1)(p-2)/6`: from the second double count
`2r₂ + 6r₃ + p = p²` and `r₂ + 1 = p`. -/
theorem card_rootCountResidues_three (hp : 5 ≤ p) :
    6 * (rootCountResidues p 3).card + 3 * p = p ^ 2 + 2 := by
  have h2 := card_rootCountResidues_two hp
  have hb := card_rootCountResidues_offDiag (p := p)
  omega

/-- **`2r₁ + p = p² + 2`**, i.e. `r₁ = p(p-1)/2 + 1`: from the first double count
`r₁ + 2r₂ + 3r₃ = p²` and the values of `r₂` and `r₃`. -/
theorem card_rootCountResidues_one (hp : 5 ≤ p) :
    2 * (rootCountResidues p 1).card + p = p ^ 2 + 2 := by
  have ha := card_rootCountResidues_incidence (p := p)
  have h2 := card_rootCountResidues_two hp
  have h3 := card_rootCountResidues_three hp
  omega

/-- **`3r₀ + 1 = p²`**, i.e. `r₀ = (p² - 1)/3`: the four classes partition the plane. -/
theorem card_rootCountResidues_zero (hp : 5 ≤ p) :
    3 * (rootCountResidues p 0).card + 1 = p ^ 2 := by
  have hs := card_rootCountResidues_sum (p := p)
  have h1 := card_rootCountResidues_one hp
  have h2 := card_rootCountResidues_two hp
  have h3 := card_rootCountResidues_three hp
  omega

/-! ### The separable one-root class

The separable depressed cubics are exactly the pairs off the cuspidal cubic, `ellipticResidues p`,
of which there are `p² - p` (`card_ellipticResidues`). Among them the root count is the Galois
orbit type of the roots: `1+1+1` (split), `1+2` (a root and an irreducible quadratic) or `3`
(irreducible). -/

variable (p) in
/-- **The separable depressed cubics with exactly one root in `𝔽_p`**: Galois orbit type `1+2`, a
rational root together with an irreducible quadratic factor. This is `rootCountResidues p 1` with
the cusp `(0, 0)` — whose cubic `X³` is a triple root, not separable — removed. -/
def oneRootResidues : Finset (ZMod p × ZMod p) :=
  ellipticResidues p ∩ rootCountResidues p 1

/-- The cusp `(0, 0)` is the one non-separable pair with exactly one root. -/
theorem rootCountResidues_one_eq_insert (hp : 5 ≤ p) :
    rootCountResidues p 1 = insert ((0, 0) : ZMod p × ZMod p) (oneRootResidues p) := by
  have hcusp : ((0, 0) : ZMod p × ZMod p) ∈ rootCountResidues p 1 := by
    rw [mem_rootCountResidues, cubicRootSet_zero, Finset.card_singleton]
  ext c
  simp only [oneRootResidues, Finset.mem_insert, Finset.mem_inter]
  constructor
  · intro hc
    by_cases hz : c = (0, 0)
    · exact Or.inl hz
    · refine Or.inr ⟨?_, hc⟩
      by_contra hell
      have hcusp' : c ∈ cuspidalResidues p := by
        simpa [ellipticResidues, cuspidalResidues] using hell
      rcases card_cubicRootSet_of_mem_cuspidalResidues hp hcusp' with ⟨h, -⟩ | ⟨-, h⟩
      · exact hz h
      · rw [mem_rootCountResidues.1 hc] at h
        exact absurd h (by norm_num)
  · rintro (rfl | ⟨-, hc⟩) <;> assumption

/-- The cusp is not separable, so it is not in `oneRootResidues p`. -/
theorem zero_notMem_oneRootResidues : ((0, 0) : ZMod p × ZMod p) ∉ oneRootResidues p := by
  intro h
  simp only [oneRootResidues, Finset.mem_inter, ellipticResidues, Finset.mem_filter,
    Finset.mem_univ, true_and] at h
  exact h.1 (by norm_num)

/-- **`2·|oneRootResidues p| + p = p²`**, i.e. `p(p-1)/2` of the `p² - p` separable depressed
cubics have exactly one root in `𝔽_p`. -/
theorem card_oneRootResidues (hp : 5 ≤ p) :
    2 * (oneRootResidues p).card + p = p ^ 2 := by
  have h := card_rootCountResidues_one hp
  rw [rootCountResidues_one_eq_insert hp,
    Finset.card_insert_of_notMem zero_notMem_oneRootResidues] at h
  omega

end WeierstrassCurve
