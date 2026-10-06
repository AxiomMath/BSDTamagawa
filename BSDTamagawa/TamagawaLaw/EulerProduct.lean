/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.TamagawaLaw.Convolution
public import BSDTamagawa.Moments.OfEulerProduct

/-!
# The Euler product of the Tamagawa law off the half-plane

For every `s : ℂ`, with no restriction on `Re(s)`, the Dirichlet series of the limiting Tamagawa
law converges absolutely and

`∑_{m ≥ 1} P_Tam(m) m^{-s} = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{-s})`.

As a consequence, every real moment of the Tamagawa law is finite and equals the product of the
local moment factors.

## Main definitions

* `WeierstrassCurve.primeSubtypeFinset`: the primes of a finite set `S ⊆ ℕ`, as a `Finset` of the
  subtype `{q : ℕ // q.Prime}`.

## Main results

* `WeierstrassCurve.tsum_truncatedTamagawaDensity_mul_cpow`: for every finite `S` and every
  `s : ℂ`, `∑_m P_Tam^S(m) m^{-s} = ∏_{p ∈ S} (∑_t δ_p(t) t^{-s})`.
* `WeierstrassCurve.tendsto_tsum_abs_sub_truncatedTamagawaDensity_mul_rpow`: for every real `x`,
  `∑_m |P_Tam(m) - P_Tam^S(m)| m^x → 0` as `S` exhausts the primes.
* `WeierstrassCurve.hasEulerProductOffHalfPlane`: the Euler product identity above, at every
  `s : ℂ`.
* `WeierstrassCurve.summable_tamagawaDensity_succ_mul_rpow`,
  `WeierstrassCurve.tsum_tamagawaDensity_succ_mul_rpow`: for every real `x`, the family
  `P_Tam(m) m^x` is summable and its sum is `∏_{p ∈ 𝒫} G_p(x)`.
* `WeierstrassCurve.summable_tamagawaDensity_succ_mul_pow`,
  `WeierstrassCurve.ofReal_tamagawaMoment_eq_tprod_momentLocalFactor`: for every integer `k ≥ 0`,
  the `k`-th moment `M_k` converges and equals `∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^k)`.

## Implementation notes

The identity is proved at a finite set `S` of primes, where `P_Tam^S` is the multiplicative
convolution of the local laws `δ_p`, `p ∈ S`, and the Dirichlet series factors by Fubini for a
finite product of absolutely convergent series. It is then passed to the limit: the moments of
`P_Tam^S` are bounded uniformly in `S`, which together with the uniform bound
`|P_Tam(m) - P_Tam^S(m)| ≤ ∑_{p ∉ S} (1 - β_p)` gives convergence of the Dirichlet series, and the
finite Euler products converge because the family of local factors is `Multipliable`. No analytic
continuation, and in particular no theorem of Landau type, is used.
-/

@[expose] public section

open Filter Topology

namespace BSDTamagawa.TamagawaEuler

/-- A nonnegative family `f : ℕ → ℝ` with `f 0 = 0` whose sums over every `[1, M]` are at most `C`
has all its finite sums at most `C`. -/
lemma sum_le_of_sum_Icc_le {f : ℕ → ℝ} {C : ℝ} (hf : ∀ m, 0 ≤ f m) (h0 : f 0 = 0)
    (hIcc : ∀ M : ℕ, ∑ m ∈ Finset.Icc 1 M, f m ≤ C) (u : Finset ℕ) : ∑ m ∈ u, f m ≤ C := by
  have hsub : u ⊆ insert 0 (Finset.Icc 1 (u.sup id)) := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_Icc.2 ⟨hpos, Finset.le_sup (f := id) hm⟩)
  calc ∑ m ∈ u, f m
      ≤ ∑ m ∈ insert 0 (Finset.Icc 1 (u.sup id)), f m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => hf m
    _ = ∑ m ∈ Finset.Icc 1 (u.sup id), f m := by rw [Finset.sum_insert (by simp), h0, zero_add]
    _ ≤ C := hIcc (u.sup id)

/-- **A tail of a moment series, at a smaller exponent.** For a nonnegative `f` with
`∑_m f(m) m^k ≤ C` and any real `x ≤ k`,

`∑_{m > M} f(m) m^{x} ≤ (M + 1)^{x - k} C`. -/
lemma tsum_shift_mul_rpow_le {f : ℕ → ℝ} {k : ℕ} {x C : ℝ} (hf : ∀ m, 0 ≤ f m) (hx : x ≤ (k : ℝ))
    (hsum : Summable fun m : ℕ => f m * (m : ℝ) ^ k)
    (hC : (∑' m : ℕ, f m * (m : ℝ) ^ k) ≤ C) (M : ℕ) :
    (∑' n : ℕ, f (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ x)
      ≤ ((M : ℝ) + 1) ^ (x - (k : ℝ)) * C := by
  have hM0 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hpow : (0 : ℝ) ≤ ((M : ℝ) + 1) ^ (x - (k : ℝ)) := Real.rpow_nonneg hM0.le _
  have hshift : Summable fun n : ℕ => f (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ k :=
    (summable_nat_add_iff (f := fun m : ℕ => f m * (m : ℝ) ^ k) (M + 1)).2 hsum
  have hterm : ∀ n : ℕ, f (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ x
      ≤ ((M : ℝ) + 1) ^ (x - (k : ℝ)) * (f (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ k) := by
    intro n
    have hpos : (0 : ℝ) < ((n + (M + 1) : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
    have hle : ((M : ℝ) + 1) ≤ ((n + (M + 1) : ℕ) : ℝ) := by
      push_cast
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsplit : ((n + (M + 1) : ℕ) : ℝ) ^ x
        = ((n + (M + 1) : ℕ) : ℝ) ^ (x - (k : ℝ)) * ((n + (M + 1) : ℕ) : ℝ) ^ k := by
      rw [← Real.rpow_natCast (((n + (M + 1) : ℕ) : ℝ)) k, ← Real.rpow_add hpos]
      congr 1
      ring
    have hmono : ((n + (M + 1) : ℕ) : ℝ) ^ (x - (k : ℝ)) ≤ ((M : ℝ) + 1) ^ (x - (k : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hM0 hle (by linarith)
    have hknn : (0 : ℝ) ≤ ((n + (M + 1) : ℕ) : ℝ) ^ k := by positivity
    calc f (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ x
        = f (n + (M + 1)) * (((n + (M + 1) : ℕ) : ℝ) ^ (x - (k : ℝ)) *
            ((n + (M + 1) : ℕ) : ℝ) ^ k) := by rw [hsplit]
      _ ≤ f (n + (M + 1)) * (((M : ℝ) + 1) ^ (x - (k : ℝ)) * ((n + (M + 1) : ℕ) : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono hknn) (hf _)
      _ = ((M : ℝ) + 1) ^ (x - (k : ℝ)) * (f (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ k) := by
          ring
  have hmaj : Summable fun n : ℕ =>
      ((M : ℝ) + 1) ^ (x - (k : ℝ)) * (f (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ k) :=
    hshift.mul_left _
  have hxsum : Summable fun n : ℕ => f (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ x :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hf _) (Real.rpow_nonneg (Nat.cast_nonneg _) x)) hterm hmaj
  have htail : (∑' n : ℕ, f (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ k) ≤ C := by
    have hsplit := hsum.sum_add_tsum_nat_add (M + 1)
    have hhead : (0 : ℝ) ≤ ∑ i ∈ Finset.range (M + 1), f i * (i : ℝ) ^ k :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hf i) (by positivity)
    linarith
  calc (∑' n : ℕ, f (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ x)
      ≤ ∑' n : ℕ,
          ((M : ℝ) + 1) ^ (x - (k : ℝ)) * (f (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ k) :=
        Summable.tsum_le_tsum hterm hxsum hmaj
    _ = ((M : ℝ) + 1) ^ (x - (k : ℝ)) *
          ∑' n : ℕ, f (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ k := tsum_mul_left
    _ ≤ ((M : ℝ) + 1) ^ (x - (k : ℝ)) * C := mul_le_mul_of_nonneg_left htail hpow

/-- For a finite family `t` of natural numbers and any `s : ℂ`, `(∏_i t_i)^s = ∏_i t_i^s` in
`ℂ`. -/
lemma prod_natCast_cpow {α : Type*} (u : Finset α) (t : α → ℕ) (s : ℂ) :
    ((∏ i ∈ u, t i : ℕ) : ℂ) ^ s = ∏ i ∈ u, ((t i : ℕ) : ℂ) ^ s := by
  classical
  refine Finset.induction_on u (by simp) fun a v ha ih => ?_
  have hmul := Complex.mul_cpow_ofReal_nonneg (a := ((t a : ℕ) : ℝ))
    (b := ((∏ i ∈ v, t i : ℕ) : ℝ)) (by positivity) (by positivity) s
  rw [Complex.ofReal_natCast, Complex.ofReal_natCast] at hmul
  rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul, hmul, ih]

end BSDTamagawa.TamagawaEuler

namespace WeierstrassCurve

open BSDTamagawa.Analysis.FinsuppFubini
open BSDTamagawa.LocalReduction BSDTamagawa.TamagawaEuler

/-! ### Moments of the `S`-truncated law, uniformly in `S` -/

/-- For every finite `S` and every integer `k ≥ 0`, the family `P_Tam^S(m) m^k` is summable. -/
theorem summable_truncatedTamagawaDensity_mul_pow (S : Finset ℕ) (k : ℕ) :
    Summable fun m : ℕ => truncatedTamagawaDensity S m * (m : ℝ) ^ k :=
  summable_of_sum_le
    (fun m => mul_nonneg (truncatedTamagawaDensity_nonneg S m) (by positivity))
    (sum_le_of_sum_Icc_le
      (fun m => mul_nonneg (truncatedTamagawaDensity_nonneg S m) (by positivity))
      (by rw [truncatedTamagawaDensity_zero, zero_mul])
      fun M => sum_truncatedTamagawaDensity_mul_pow_le S k M)

/-- For every finite `S` and every integer `k ≥ 0`, `∑_m P_Tam^S(m) m^k ≤ C_k`, with
`C_k = tamagawaMomentBound k` independent of `S`. -/
theorem tsum_truncatedTamagawaDensity_mul_pow_le (S : Finset ℕ) (k : ℕ) :
    (∑' m : ℕ, truncatedTamagawaDensity S m * (m : ℝ) ^ k) ≤ tamagawaMomentBound (k : ℝ) :=
  Real.tsum_le_of_sum_le
    (fun m => mul_nonneg (truncatedTamagawaDensity_nonneg S m) (by positivity))
    (sum_le_of_sum_Icc_le
      (fun m => mul_nonneg (truncatedTamagawaDensity_nonneg S m) (by positivity))
      (by rw [truncatedTamagawaDensity_zero, zero_mul])
      fun M => sum_truncatedTamagawaDensity_mul_pow_le S k M)

/-- For every integer `k ≥ 0`, `∑_m P_Tam(m) m^k ≤ C_k`, with `C_k = tamagawaMomentBound k`. -/
theorem tsum_tamagawaDensity_mul_pow_le (k : ℕ) :
    (∑' m : ℕ, tamagawaDensity m * (m : ℝ) ^ k) ≤ tamagawaMomentBound (k : ℝ) :=
  Real.tsum_le_of_sum_le
    (fun m => mul_nonneg (tamagawaDensity_nonneg m) (by positivity))
    (sum_le_of_sum_Icc_le
      (fun m => mul_nonneg (tamagawaDensity_nonneg m) (by positivity))
      (by rw [tamagawaDensity_zero, zero_mul])
      fun M => sum_tamagawaDensity_mul_pow_le k M)

/-- For every finite `S` and every real `x`, the family `P_Tam^S(m) m^x` is summable. -/
theorem summable_truncatedTamagawaDensity_mul_rpow (S : Finset ℕ) (x : ℝ) :
    Summable fun m : ℕ => truncatedTamagawaDensity S m * (m : ℝ) ^ x := by
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (truncatedTamagawaDensity_nonneg S m)
      (Real.rpow_nonneg (by positivity) x))
    (fun m => ?_) (summable_truncatedTamagawaDensity_mul_pow S ⌈x⌉₊)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [truncatedTamagawaDensity_zero, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left ?_ (truncatedTamagawaDensity_nonneg S m)
    rw [← Real.rpow_natCast (m : ℝ) ⌈x⌉₊]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (Nat.le_ceil x)

/-! ### The Euler product for the `S`-truncated law, at every `s : ℂ` -/

/-- For every `p` and every `s : ℂ`, the local Dirichlet series `∑_t δ_p(t) t^{-s}` converges
absolutely. -/
lemma summable_norm_localDensity_mul_cpow (p : ℕ) (s : ℂ) :
    Summable fun t : ℕ => ‖((localDensity p t : ℝ) : ℂ) * (t : ℂ) ^ (-s)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => ?_)
    (summable_localDensity_mul_rpow p (-s.re))
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [localDensity_zero]
    simp
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (localDensity_nonneg p t),
      Complex.norm_natCast_cpow_of_pos ht, Complex.neg_re]

/-- **The Euler product for the `S`-truncated law.** For every finite `S` and every `s : ℂ`, with
no restriction on `Re(s)`,

`∑_{m} P_Tam^S(m) m^{-s} = ∏_{p ∈ S prime} (∑_{t ≥ 0} δ_p(t) t^{-s})`. -/
theorem tsum_truncatedTamagawaDensity_mul_cpow (S : Finset ℕ) (s : ℂ) :
    ∑' m : ℕ, ((truncatedTamagawaDensity S m : ℝ) : ℂ) * (m : ℂ) ^ (-s)
      = ∏ p : ↥(S.filter Nat.Prime),
          ∑' t : ℕ, ((localDensity (p : ℕ) t : ℝ) : ℂ) * (t : ℂ) ^ (-s) := by
  classical
  have hF := hasSum_finsuppProd
    (fun (p : ↥(S.filter Nat.Prime)) (t : ℕ) => ((localDensity (p : ℕ) t : ℝ) : ℂ) * (t : ℂ) ^ (-s))
    fun p => summable_norm_localDensity_mul_cpow (p : ℕ) s
  have hF' : HasSum (fun t : ↥(S.filter Nat.Prime) → ℕ =>
        ∏ p : ↥(S.filter Nat.Prime), ((localDensity (p : ℕ) (t p) : ℝ) : ℂ) * (t p : ℂ) ^ (-s))
      (∏ p : ↥(S.filter Nat.Prime),
        ∑' t : ℕ, ((localDensity (p : ℕ) t : ℝ) : ℂ) * (t : ℂ) ^ (-s)) :=
    ((Equiv.hasSum_iff (Finsupp.equivFunOnFinite (α := ↥(S.filter Nat.Prime)) (M := ℕ)).symm).mpr
      hF).congr_fun fun t => by simp
  have hsummand : ∀ t : ↥(S.filter Nat.Prime) → ℕ,
      (∏ p : ↥(S.filter Nat.Prime), ((localDensity (p : ℕ) (t p) : ℝ) : ℂ) * (t p : ℂ) ^ (-s))
        = ((∏ p : ↥(S.filter Nat.Prime), localDensity (p : ℕ) (t p) : ℝ) : ℂ) *
            ((∏ p : ↥(S.filter Nat.Prime), t p : ℕ) : ℂ) ^ (-s) := by
    intro t
    rw [Finset.prod_mul_distrib, Complex.ofReal_prod,
      prod_natCast_cpow Finset.univ (fun p : ↥(S.filter Nat.Prime) => t p) (-s)]
  have hfib := hF'.tsum_fiberwise
    (fun t : ↥(S.filter Nat.Prime) → ℕ => ∏ p : ↥(S.filter Nat.Prime), t p)
  refine (hfib.congr_fun fun m => ?_).tsum_eq
  rcases eq_or_ne m 0 with rfl | hm
  · have hzero : ∀ b : ↑((fun t : ↥(S.filter Nat.Prime) → ℕ =>
          ∏ p : ↥(S.filter Nat.Prime), t p) ⁻¹' {0}),
        (∏ p : ↥(S.filter Nat.Prime),
          ((localDensity (p : ℕ) ((b : ↥(S.filter Nat.Prime) → ℕ) p) : ℝ) : ℂ) *
            (((b : ↥(S.filter Nat.Prime) → ℕ) p : ℕ) : ℂ) ^ (-s)) = 0 := by
      intro b
      obtain ⟨p, -, hp0⟩ := Finset.prod_eq_zero_iff.1 (show
        (∏ p : ↥(S.filter Nat.Prime), (b : ↥(S.filter Nat.Prime) → ℕ) p) = 0 from b.2)
      refine Finset.prod_eq_zero (Finset.mem_univ p) ?_
      rw [hp0, localDensity_zero, Complex.ofReal_zero, zero_mul]
    rw [truncatedTamagawaDensity_zero, Complex.ofReal_zero, zero_mul, tsum_congr hzero, tsum_zero]
  · have hset : ∀ t : ↥(S.filter Nat.Prime) → ℕ,
        t ∈ (fun u : ↥(S.filter Nat.Prime) → ℕ => ∏ p : ↥(S.filter Nat.Prime), u p) ⁻¹' {m} ↔
          t ∈ tamagawaTupleFactorizations S m := by
      intro t
      rw [mem_tamagawaTupleFactorizations_iff S hm]
      exact Iff.rfl
    have hswap := Equiv.tsum_eq (Equiv.subtypeEquivRight hset).symm
      (fun b : ↑((fun u : ↥(S.filter Nat.Prime) → ℕ => ∏ p : ↥(S.filter Nat.Prime), u p) ⁻¹' {m}) =>
        ∏ p : ↥(S.filter Nat.Prime),
          ((localDensity (p : ℕ) ((b : ↥(S.filter Nat.Prime) → ℕ) p) : ℝ) : ℂ) *
            (((b : ↥(S.filter Nat.Prime) → ℕ) p : ℕ) : ℂ) ^ (-s))
    rw [← hswap, tsum_fintype, truncatedTamagawaDensity_eq, Complex.ofReal_sum, Finset.sum_mul,
      ← Finset.sum_finset_coe]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 := hsummand (c : ↥(S.filter Nat.Prime) → ℕ)
    rw [(mem_tamagawaTupleFactorizations_iff S hm _).1 c.2] at h1
    exact h1.symm

/-! ### The primes of `S`, as a `Finset` of the subtype `𝒫` -/

/-- The primes of a finite set `S ⊆ ℕ`, as a `Finset` of `𝒫 = {q : ℕ // q.Prime}`. -/
noncomputable def primeSubtypeFinset (S : Finset ℕ) : Finset {q : ℕ // q.Prime} :=
  (S.filter Nat.Prime).attach.map
    ⟨fun x : ↥(S.filter Nat.Prime) => ⟨(x : ℕ), (Finset.mem_filter.1 x.2).2⟩,
      fun x y h => Subtype.ext (by simpa using h)⟩

/-- A prime `p` lies in `primeSubtypeFinset S` if and only if `p ∈ S`. -/
@[simp] lemma mem_primeSubtypeFinset {S : Finset ℕ} {p : {q : ℕ // q.Prime}} :
    p ∈ primeSubtypeFinset S ↔ (p : ℕ) ∈ S := by
  rw [primeSubtypeFinset, Finset.mem_map]
  refine ⟨fun h => ?_, fun hp => ?_⟩
  · obtain ⟨x, -, hx⟩ := h
    have hval : (x : ℕ) = (p : ℕ) := congrArg Subtype.val hx
    rw [← hval]
    exact (Finset.mem_filter.1 x.2).1
  · exact ⟨⟨(p : ℕ), Finset.mem_filter.2 ⟨hp, p.2⟩⟩, Finset.mem_attach _ _, rfl⟩

/-- At a prime `p`, the local Euler factor is `L_p(s) = ∑_{t ≥ 0} δ_p(t) t^{-s}`. -/
lemma tamagawaEulerFactor_eq_tsum_localDensity (p : {q : ℕ // q.Prime}) (s : ℂ) :
    tamagawaEulerFactor p s
      = ∑' t : ℕ, ((localDensity (p : ℕ) t : ℝ) : ℂ) * (t : ℂ) ^ (-s) := by
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  rw [tamagawaEulerFactor_def]
  exact tsum_congr fun t => by rw [localDensity_of_prime]

/-- For every finite `S` and every `s : ℂ`, the product of the local Euler factors over the primes
of `S` is `∏_{p ∈ S prime} (∑_t δ_p(t) t^{-s})`. -/
lemma prod_primeSubtypeFinset (S : Finset ℕ) (s : ℂ) :
    ∏ p ∈ primeSubtypeFinset S, tamagawaEulerFactor p s
      = ∏ p : ↥(S.filter Nat.Prime),
          ∑' t : ℕ, ((localDensity (p : ℕ) t : ℝ) : ℂ) * (t : ℂ) ^ (-s) := by
  rw [primeSubtypeFinset, Finset.prod_map, Finset.attach_eq_univ]
  exact Finset.prod_congr rfl fun x _ => tamagawaEulerFactor_eq_tsum_localDensity _ s

/-- `primeSubtypeFinset (Finset.range N)` tends to `atTop` in `Finset 𝒫` as `N → ∞`. -/
lemma tendsto_primeSubtypeFinset_range :
    Tendsto (fun N : ℕ => primeSubtypeFinset (Finset.range N)) atTop atTop :=
  Filter.tendsto_atTop_atTop.2 fun T =>
    ⟨(T.image fun p : {q : ℕ // q.Prime} => (p : ℕ)).sup id + 1, fun _N hN _q hq =>
      mem_primeSubtypeFinset.2 (Finset.mem_range.2 (lt_of_le_of_lt
        (Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hq)) hN))⟩

/-- For every `s : ℂ`, the finite Euler products `∏_{p < N prime} (∑_t δ_p(t) t^{-s})` tend to
`∏'_{p ∈ 𝒫} L_p(s)` as `N → ∞`. -/
lemma tendsto_prod_localDensity_mul_cpow (s : ℂ) :
    Tendsto (fun N : ℕ => ∏ p : ↥((Finset.range N).filter Nat.Prime),
        ∑' t : ℕ, ((localDensity (p : ℕ) t : ℝ) : ℂ) * (t : ℂ) ^ (-s)) atTop
      (𝓝 (∏' p : {q : ℕ // q.Prime}, tamagawaEulerFactor p s)) := by
  have hprod : Tendsto (fun u : Finset {q : ℕ // q.Prime} => ∏ p ∈ u, tamagawaEulerFactor p s)
      atTop (𝓝 (∏' p : {q : ℕ // q.Prime}, tamagawaEulerFactor p s)) :=
    (multipliable_tamagawaEulerFactor s).hasProd
  exact (hprod.comp tendsto_primeSubtypeFinset_range).congr fun N =>
    prod_primeSubtypeFinset (Finset.range N) s

/-! ### Weighted `L¹` convergence of the truncated laws -/

/-- For every finite `S` and every real `x`, the family `|P_Tam(m) - P_Tam^S(m)| m^x` is
summable. -/
lemma summable_abs_sub_truncatedTamagawaDensity_mul_rpow (S : Finset ℕ) (x : ℝ) :
    Summable fun m : ℕ =>
      |tamagawaDensity m - truncatedTamagawaDensity S m| * (m : ℝ) ^ x := by
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg m) x)) (fun m => ?_)
    ((summable_tamagawaDensity_mul_rpow x).add (summable_truncatedTamagawaDensity_mul_rpow S x))
  have h1 : |tamagawaDensity m - truncatedTamagawaDensity S m|
      ≤ tamagawaDensity m + truncatedTamagawaDensity S m := by
    rw [abs_le]
    constructor <;>
      linarith [tamagawaDensity_nonneg m, truncatedTamagawaDensity_nonneg S m]
  calc |tamagawaDensity m - truncatedTamagawaDensity S m| * (m : ℝ) ^ x
      ≤ (tamagawaDensity m + truncatedTamagawaDensity S m) * (m : ℝ) ^ x :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg m) x)
    _ = tamagawaDensity m * (m : ℝ) ^ x + truncatedTamagawaDensity S m * (m : ℝ) ^ x := by ring

/-- For two nonnegative families `P`, `Q` whose `k`-th moments are both at most `C` and whose
difference is uniformly at most `b`, for any real `x ≤ k` and any `M`,

`∑_m |P(m) - Q(m)| m^x ≤ b ∑_{m ≤ M} m^x + 2 (M+1)^{x-k} C`. -/
lemma tsum_abs_sub_mul_rpow_le {P Q : ℕ → ℝ} {b C x : ℝ} {k : ℕ}
    (hP : ∀ m, 0 ≤ P m) (hQ : ∀ m, 0 ≤ Q m) (hb : ∀ m, |P m - Q m| ≤ b) (hxk : x ≤ (k : ℝ))
    (hPsum : Summable fun m : ℕ => P m * (m : ℝ) ^ k)
    (hPC : (∑' m : ℕ, P m * (m : ℝ) ^ k) ≤ C)
    (hQsum : Summable fun m : ℕ => Q m * (m : ℝ) ^ k)
    (hQC : (∑' m : ℕ, Q m * (m : ℝ) ^ k) ≤ C)
    (hPx : Summable fun m : ℕ => P m * (m : ℝ) ^ x)
    (hQx : Summable fun m : ℕ => Q m * (m : ℝ) ^ x)
    (M : ℕ) :
    (∑' m : ℕ, |P m - Q m| * (m : ℝ) ^ x)
      ≤ b * (∑ i ∈ Finset.range (M + 1), (i : ℝ) ^ x)
        + (((M : ℝ) + 1) ^ (x - (k : ℝ)) * C + ((M : ℝ) + 1) ^ (x - (k : ℝ)) * C) := by
  have hnn : ∀ m : ℕ, (0 : ℝ) ≤ (m : ℝ) ^ x := fun m => Real.rpow_nonneg (Nat.cast_nonneg m) x
  have hdom : ∀ m : ℕ, |P m - Q m| * (m : ℝ) ^ x ≤ P m * (m : ℝ) ^ x + Q m * (m : ℝ) ^ x := by
    intro m
    have h1 : |P m - Q m| ≤ P m + Q m := by
      rw [abs_le]
      constructor <;> linarith [hP m, hQ m]
    calc |P m - Q m| * (m : ℝ) ^ x ≤ (P m + Q m) * (m : ℝ) ^ x :=
          mul_le_mul_of_nonneg_right h1 (hnn m)
      _ = P m * (m : ℝ) ^ x + Q m * (m : ℝ) ^ x := by ring
  have hDsum : Summable fun m : ℕ => |P m - Q m| * (m : ℝ) ^ x :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _) (hnn m)) hdom (hPx.add hQx)
  have hsplit := hDsum.sum_add_tsum_nat_add (M + 1)
  have hhead : (∑ i ∈ Finset.range (M + 1), |P i - Q i| * (i : ℝ) ^ x)
      ≤ b * ∑ i ∈ Finset.range (M + 1), (i : ℝ) ^ x := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hb i) (hnn i)
  have hs1 : Summable fun n : ℕ => P (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ x :=
    (summable_nat_add_iff (f := fun m : ℕ => P m * (m : ℝ) ^ x) (M + 1)).2 hPx
  have hs2 : Summable fun n : ℕ => Q (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ x :=
    (summable_nat_add_iff (f := fun m : ℕ => Q m * (m : ℝ) ^ x) (M + 1)).2 hQx
  have hsD : Summable fun n : ℕ =>
      |P (n + (M + 1)) - Q (n + (M + 1))| * ((n + (M + 1) : ℕ) : ℝ) ^ x :=
    (summable_nat_add_iff (f := fun m : ℕ => |P m - Q m| * (m : ℝ) ^ x) (M + 1)).2 hDsum
  have htail : (∑' n : ℕ, |P (n + (M + 1)) - Q (n + (M + 1))| * ((n + (M + 1) : ℕ) : ℝ) ^ x)
      ≤ ((M : ℝ) + 1) ^ (x - (k : ℝ)) * C + ((M : ℝ) + 1) ^ (x - (k : ℝ)) * C := by
    calc (∑' n : ℕ, |P (n + (M + 1)) - Q (n + (M + 1))| * ((n + (M + 1) : ℕ) : ℝ) ^ x)
        ≤ ∑' n : ℕ, (P (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ x
            + Q (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ x) :=
          Summable.tsum_le_tsum (fun n => hdom _) hsD (hs1.add hs2)
      _ = (∑' n : ℕ, P (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ x)
            + ∑' n : ℕ, Q (n + (M + 1)) * ((n + (M + 1) : ℕ) : ℝ) ^ x := hs1.tsum_add hs2
      _ ≤ ((M : ℝ) + 1) ^ (x - (k : ℝ)) * C + ((M : ℝ) + 1) ^ (x - (k : ℝ)) * C :=
          add_le_add (tsum_shift_mul_rpow_le hP hxk hPsum hPC M)
            (tsum_shift_mul_rpow_le hQ hxk hQsum hQC M)
  linarith

/-- For every `x : ℝ`, `∑_m |P_Tam(m) - P_Tam^S(m)| m^x → 0` as `S = [0, N)` with `N → ∞`. -/
theorem tendsto_tsum_abs_sub_truncatedTamagawaDensity_mul_rpow (x : ℝ) :
    Tendsto (fun N : ℕ => ∑' m : ℕ,
        |tamagawaDensity m - truncatedTamagawaDensity (Finset.range N) m| * (m : ℝ) ^ x)
      atTop (𝓝 0) := by
  obtain ⟨k, hxk⟩ : ∃ k : ℕ, x < (k : ℝ) := by
    refine ⟨⌈x⌉₊ + 1, ?_⟩
    have := Nat.le_ceil x
    push_cast
    linarith
  refine tendsto_order.2 ⟨fun a ha => ?_, fun ε hε => ?_⟩
  · filter_upwards with N
    exact lt_of_lt_of_le ha (tsum_nonneg fun m =>
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg m) x))
  obtain ⟨M, hM⟩ : ∃ M : ℕ,
      ((M : ℝ) + 1) ^ (x - (k : ℝ)) * tamagawaMomentBound (k : ℝ)
        + ((M : ℝ) + 1) ^ (x - (k : ℝ)) * tamagawaMomentBound (k : ℝ) < ε / 2 := by
    have h0 : Tendsto (fun r : ℝ => r ^ (x - (k : ℝ))) atTop (𝓝 0) := by
      simpa [neg_sub] using tendsto_rpow_neg_atTop (y := (k : ℝ) - x) (by linarith)
    have h1 : Tendsto (fun M : ℕ => ((M : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 := ((h0.comp h1).mul_const (tamagawaMomentBound (k : ℝ)))
    have h3 : Tendsto (fun M : ℕ =>
        ((M : ℝ) + 1) ^ (x - (k : ℝ)) * tamagawaMomentBound (k : ℝ)
          + ((M : ℝ) + 1) ^ (x - (k : ℝ)) * tamagawaMomentBound (k : ℝ)) atTop (𝓝 0) := by
      simpa using h2.add h2
    exact (h3.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))).exists
  have hbtend : Tendsto (fun N : ℕ =>
      (∑' p : ℕ, if p ∈ Finset.range N then (0 : ℝ) else betaDefect p)
        * ∑ i ∈ Finset.range (M + 1), (i : ℝ) ^ x) atTop (𝓝 0) := by
    simpa using (tendsto_tsum_betaDefect_compl.comp Filter.tendsto_finset_range).mul_const
      (∑ i ∈ Finset.range (M + 1), (i : ℝ) ^ x)
  filter_upwards [eventually_ge_atTop 4,
    hbtend.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))] with N hN4 hNb
  have hb : ∀ m : ℕ, |tamagawaDensity m - truncatedTamagawaDensity (Finset.range N) m|
      ≤ ∑' p : ℕ, if p ∈ Finset.range N then (0 : ℝ) else betaDefect p := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · rw [tamagawaDensity_zero, truncatedTamagawaDensity_zero, sub_self, abs_zero]
      exact tsum_nonneg fun p => by split; exacts [le_rfl, betaDefect_nonneg p]
    · exact abs_tamagawaDensity_sub_truncatedTamagawaDensity_le _ hm
        (Finset.mem_range.2 (by omega)) (Finset.mem_range.2 (by omega))
  have hest := tsum_abs_sub_mul_rpow_le (P := tamagawaDensity)
    (Q := truncatedTamagawaDensity (Finset.range N)) (x := x) (k := k)
    (C := tamagawaMomentBound (k : ℝ)) tamagawaDensity_nonneg
    (truncatedTamagawaDensity_nonneg _) hb hxk.le
    (summable_tamagawaDensity_mul_pow k) (tsum_tamagawaDensity_mul_pow_le k)
    (summable_truncatedTamagawaDensity_mul_pow _ k)
    (tsum_truncatedTamagawaDensity_mul_pow_le _ k)
    (summable_tamagawaDensity_mul_rpow x)
    (summable_truncatedTamagawaDensity_mul_rpow _ x) M
  linarith

/-! ### The Euler product at every `s : ℂ` -/

/-- For every finite `S` and every `s : ℂ`, the Dirichlet series `∑_m P_Tam^S(m) m^{-s}` converges
absolutely. -/
lemma summable_norm_truncatedTamagawaDensity_mul_cpow (S : Finset ℕ) (s : ℂ) :
    Summable fun m : ℕ => ‖((truncatedTamagawaDensity S m : ℝ) : ℂ) * (m : ℂ) ^ (-s)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (summable_truncatedTamagawaDensity_mul_rpow S (-s.re))
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [truncatedTamagawaDensity_zero]
    simp
  · rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (truncatedTamagawaDensity_nonneg S m),
      Complex.norm_natCast_cpow_of_pos hm, Complex.neg_re]

/-- For every `s : ℂ`, `∑_m P_Tam^S(m) m^{-s} → ∑_m P_Tam(m) m^{-s}` as `S = [0, N)` with
`N → ∞`. -/
lemma tendsto_tsum_truncatedTamagawaDensity_mul_cpow (s : ℂ) :
    Tendsto (fun N : ℕ => ∑' m : ℕ,
        ((truncatedTamagawaDensity (Finset.range N) m : ℝ) : ℂ) * (m : ℂ) ^ (-s)) atTop
      (𝓝 (∑' m : ℕ, (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s))) := by
  have hPc : Summable fun m : ℕ => (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s) :=
    Summable.of_norm (summable_norm_tamagawaDensity_mul_cpow_all s)
  have hdiff : Tendsto (fun N : ℕ =>
      (∑' m : ℕ, ((truncatedTamagawaDensity (Finset.range N) m : ℝ) : ℂ) * (m : ℂ) ^ (-s))
        - ∑' m : ℕ, (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
      (tendsto_tsum_abs_sub_truncatedTamagawaDensity_mul_rpow (-s.re))
    filter_upwards with N
    have habs := summable_abs_sub_truncatedTamagawaDensity_mul_rpow (Finset.range N) (-s.re)
    have hb : ∀ m : ℕ,
        ‖((truncatedTamagawaDensity (Finset.range N) m : ℝ) : ℂ) * (m : ℂ) ^ (-s)
            - (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)‖
          ≤ |tamagawaDensity m - truncatedTamagawaDensity (Finset.range N) m| *
              (m : ℝ) ^ (-s.re) := by
      intro m
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_sub_comm]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [tamagawaDensity_zero, truncatedTamagawaDensity_zero, sub_self, abs_zero, zero_mul,
          zero_mul]
      · rw [Complex.norm_natCast_cpow_of_pos hm, Complex.neg_re]
    have hnorms : Summable fun m : ℕ =>
        ‖((truncatedTamagawaDensity (Finset.range N) m : ℝ) : ℂ) * (m : ℂ) ^ (-s)
          - (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb habs
    rw [← Summable.tsum_sub (Summable.of_norm
      (summable_norm_truncatedTamagawaDensity_mul_cpow (Finset.range N) s)) hPc]
    exact le_trans (norm_tsum_le_tsum_norm hnorms) (Summable.tsum_le_tsum hb hnorms habs)
  simpa using hdiff.add_const (∑' m : ℕ, (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s))

/-- For every `s : ℂ`, with no restriction on `Re(s)`,

`∑_{m ≥ 1} P_Tam(m) m^{-s} = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{-s})`. -/
theorem tsum_tamagawaDensity_mul_cpow_all (s : ℂ) :
    ∑' m : ℕ, (tamagawaDensity m : ℂ) * (m : ℂ) ^ (-s)
      = ∏' p : {q : ℕ // q.Prime}, tamagawaEulerFactor p s :=
  tendsto_nhds_unique (tendsto_tsum_truncatedTamagawaDensity_mul_cpow s)
    ((tendsto_prod_localDensity_mul_cpow s).congr fun N =>
      (tsum_truncatedTamagawaDensity_mul_cpow (Finset.range N) s).symm)

/-- For every `s : ℂ` at which the Euler product `∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{-s})` converges
absolutely, with no restriction on `Re(s)`, the Dirichlet series `∑_{m ≥ 1} P_Tam(m) m^{-s}`
converges absolutely and

`∑_{m ≥ 1} P_Tam(m) m^{-s} = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{-s})`. -/
@[bsd_tamagawa "T018o"]
theorem hasEulerProductOffHalfPlane : HasEulerProductOffHalfPlane :=
  hasEulerProductOffHalfPlane_iff_tsum_eq.2 tsum_tamagawaDensity_mul_cpow_all

/-! ### Moments of the Tamagawa law -/

/-- For every real `x` the family `(P_Tam(m) m^{x})_{m ≥ 1}` is summable. -/
@[bsd_tamagawa "T059i"]
theorem summable_tamagawaDensity_succ_mul_rpow (x : ℝ) :
    Summable fun n : ℕ => tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ x :=
  summable_tamagawaDensity_succ_mul_rpow_of_euler hasEulerProductOffHalfPlane x

/-- For every real `x`,

`∑_{m ≥ 1} P_Tam(m) m^{x} = ∏_{p ∈ 𝒫} G_p(x)`,

with `G_p = momentLocalFactor p` the local moment factor. -/
@[bsd_tamagawa "T059i"]
theorem tsum_tamagawaDensity_succ_mul_rpow (x : ℝ) :
    ((∑' n : ℕ, tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ x : ℝ) : ℂ)
      = ∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) x :=
  tsum_tamagawaDensity_succ_mul_rpow_of_euler hasEulerProductOffHalfPlane x

/-- For every integer `k ≥ 0` the family `(P_Tam(m) m^{k})_{m ≥ 1}` is summable, so the `k`-th
moment `M_k = ∑_{m ≥ 1} P_Tam(m) m^{k}` converges absolutely. -/
@[bsd_tamagawa "T059a"]
theorem summable_tamagawaDensity_succ_mul_pow (k : ℕ) :
    Summable fun n : ℕ => tamagawaDensity (n + 1) * ((n + 1 : ℕ) : ℝ) ^ k :=
  summable_tamagawaDensity_succ_mul_pow_of_euler k hasEulerProductOffHalfPlane

/-- For every integer `k ≥ 0`,

`M_k = ∏_{p ∈ 𝒫} (∑_{t ≥ 1} δ_p(t) t^{k})`,

with `M_k = tamagawaMoment k` and the local factor `momentLocalFactor p k`. -/
@[bsd_tamagawa "T059a"]
theorem ofReal_tamagawaMoment_eq_tprod_momentLocalFactor (k : ℕ) :
    ((tamagawaMoment k : ℝ) : ℂ)
      = ∏' p : {q : ℕ // q.Prime}, momentLocalFactor (p : ℕ) (k : ℝ) :=
  ofReal_tamagawaMoment_eq_tprod_momentLocalFactor_of_euler k hasEulerProductOffHalfPlane

end WeierstrassCurve
