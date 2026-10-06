/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import BSDTamagawa.LocalDensity.K0Mass

/-!
# The local Euler factor under a bounded local weight

If the local weight `Φ` is bounded by `M ≥ 1` on all of `𝒦`, then the master Euler factor satisfies

  `|β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮)| ≤ 1 + 9M/p²`

for every prime `p`. Here `β_p` is the trivial-stratum mass (`WeierstrassCurve.β`), `δ_p(K)` the
local reduction density (`WeierstrassCurve.deltaP`), `Φ` the local weight
(`WeierstrassCurve.localWeight`) and `𝒦₀ = {(I₀, 1), (I₁, 1)}`. Writing `T := ∑_{K ∉ 𝒦₀} δ_p(K)`,
one has `β_p + T = 1` and `T ≤ 9/p²`, so the left side is at most
`β_p + M·T = 1 + (M - 1)·T ≤ 1 + 9M/p²`.

## Main results

* `WeierstrassCurve.β_toReal_add_tsum_compl_K0_toReal`: `β_p + ∑_{K ∉ 𝒦₀} δ_p(K) = 1` in `ℝ`.
* `WeierstrassCurve.tsum_compl_K0_toReal_le_nine_div_sq`: `∑_{K ∉ 𝒦₀} δ_p(K) ≤ 9/p²` in `ℝ`.
* `WeierstrassCurve.norm_tsum_compl_K0_localWeight_le`:
  `‖∑_{K ∉ 𝒦₀} δ_p(K) Φ(K)‖ ≤ (∑_{K ∉ 𝒦₀} δ_p(K)) · M`.
* `WeierstrassCurve.norm_localFactor_le_one_add_nine_mul_div_sq`: the bound displayed above.
* `WeierstrassCurve.exists_bounded_localFactor_bound`: the existential form, with constants `C > 0`
  and `p₀` uniform in `Λ`, `Π`, the parameters and `M`.
-/

@[expose] public section

namespace WeierstrassCurve

open BSDTamagawa.LocalReduction BSDTamagawa.KodairaParam

open scoped ENNReal

variable (p : ℕ) [Fact p.Prime]

/-! ### The nontrivial mass, in `ℝ` -/

/-- The reduction density outside `𝒦₀` has finite total mass: `∑_{K ∉ 𝒦₀} δ_p(K) ≠ ⊤`. -/
theorem tsum_compl_K0_ne_top : ∑' K : ↥(K0ᶜ : Set ReductionData), deltaP p K ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (by rw [← β_add_tsum_compl_K0 p]; exact le_add_self)

/-- The real-valued reduction densities `K ↦ δ_p(K)` on `𝒦 ∖ 𝒦₀` are summable. -/
theorem summable_deltaP_toReal_compl_K0 :
    Summable fun K : ↥(K0ᶜ : Set ReductionData) => (deltaP p (K : ReductionData)).toReal :=
  ENNReal.summable_toReal (tsum_compl_K0_ne_top p)

/-- `β_p + ∑_{K ∉ 𝒦₀} δ_p(K) = 1`, with all masses taken in `ℝ`. -/
theorem β_toReal_add_tsum_compl_K0_toReal :
    (β p).toReal
        + ∑' K : ↥(K0ᶜ : Set ReductionData), (deltaP p (K : ReductionData)).toReal = 1 := by
  have h := congrArg ENNReal.toReal (β_add_tsum_compl_K0 p)
  rwa [ENNReal.toReal_add (β_ne_top p) (tsum_compl_K0_ne_top p),
    ENNReal.tsum_toReal_eq (fun K => deltaP_ne_top p _), ENNReal.toReal_one] at h

/-- `1 ≤ β_p + 9/p²` in `ℝ`, for every prime `p`. -/
theorem one_le_β_toReal_add_nine_div_sq : 1 ≤ (β p).toReal + 9 / (p : ℝ) ^ 2 := by
  have hpne : p ≠ 0 := (Fact.out : p.Prime).pos.ne'
  have hp0 : ((p : ℝ≥0∞)) ^ 2 ≠ 0 := pow_ne_zero 2 (by simpa using hpne)
  have hdiv : (9 : ℝ≥0∞) / (p : ℝ≥0∞) ^ 2 ≠ ⊤ := ENNReal.div_ne_top (by norm_num) hp0
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨β_ne_top p, hdiv⟩)
    (one_le_β_add_nine_div_sq p)
  rwa [ENNReal.toReal_one, ENNReal.toReal_add (β_ne_top p) hdiv, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_natCast] at h

/-- `∑_{K ∉ 𝒦₀} δ_p(K) ≤ 9/p²` in `ℝ`, for every prime `p`. -/
theorem tsum_compl_K0_toReal_le_nine_div_sq :
    ∑' K : ↥(K0ᶜ : Set ReductionData), (deltaP p (K : ReductionData)).toReal
      ≤ 9 / (p : ℝ) ^ 2 := by
  linarith [β_toReal_add_tsum_compl_K0_toReal p, one_le_β_toReal_add_nine_div_sq p]

/-! ### The sup bound on the non-`𝒦₀` block -/

/-- If `‖Φ(K)‖ ≤ M` for every `K ∈ 𝒦`, then
`‖∑_{K ∉ 𝒦₀} δ_p(K) Φ(K)‖ ≤ (∑_{K ∉ 𝒦₀} δ_p(K)) · M`. -/
theorem norm_tsum_compl_K0_localWeight_le {Λ : Finset ReductionData} {P : Finset ℕ}
    (s u w : ℂ) (z : P → ℂ) (uΛ : Λ → ℂ) {M : ℝ}
    (hbdd : ∀ K : ReductionData, ‖localWeight Λ P K s u w z uΛ‖ ≤ M) :
    ‖∑' K : ↥(K0ᶜ : Set ReductionData), ((deltaP p (K : ReductionData)).toReal : ℂ)
          * localWeight Λ P (K : ReductionData) s u w z uΛ‖
      ≤ (∑' K : ↥(K0ᶜ : Set ReductionData), (deltaP p (K : ReductionData)).toReal) * M := by
  refine tsum_of_norm_bounded ((summable_deltaP_toReal_compl_K0 p).hasSum.mul_right M) fun K => ?_
  rw [norm_mul, Complex.norm_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hbdd _) ENNReal.toReal_nonneg

/-- If `0 ≤ D`, `T ≤ D` and `1 ≤ M`, then `(1 - T) + T·M ≤ 1 + D·M`. -/
private lemma one_sub_add_mul_le {T M D : ℝ} (hTD : T ≤ D) (hD : 0 ≤ D) (hM : 1 ≤ M) :
    1 - T + T * M ≤ 1 + D * M := by
  nlinarith [mul_le_mul_of_nonneg_right hTD (sub_nonneg.2 hM)]

/-! ### The bound on the local Euler factor -/

/-- Let `Λ` be a finite set of reduction data, `Π` a finite set of primes, and `(s, u, w, 𝐳, 𝐮)`
arbitrary parameters. If `M ≥ 1` bounds the local weight uniformly, `‖Φ(K; s, u, w, 𝐳, 𝐮)‖ ≤ M` for
every `K ∈ 𝒦`, then at every prime `p`

  `‖β_p + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_p(K) Φ(K; s, u, w, 𝐳, 𝐮)‖ ≤ 1 + 9M/p²`. -/
@[bsd_tamagawa "T023c"]
theorem norm_localFactor_le_one_add_nine_mul_div_sq {Λ : Finset ReductionData} {P : Finset ℕ}
    (s u w : ℂ) (z : P → ℂ) (uΛ : Λ → ℂ) {M : ℝ} (hM : 1 ≤ M)
    (hbdd : ∀ K : ReductionData, ‖localWeight Λ P K s u w z uΛ‖ ≤ M) :
    ‖((β p).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
          ((deltaP p (K : ReductionData)).toReal : ℂ)
            * localWeight Λ P (K : ReductionData) s u w z uΛ‖
      ≤ 1 + 9 * M / (p : ℝ) ^ 2 := by
  have hD : (0 : ℝ) ≤ 9 / (p : ℝ) ^ 2 := by positivity
  have hmass := β_toReal_add_tsum_compl_K0_toReal p
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_of_nonneg ENNReal.toReal_nonneg]
  refine (add_le_add le_rfl (norm_tsum_compl_K0_localWeight_le p s u w z uΛ hbdd)).trans ?_
  rw [show (β p).toReal
      = 1 - ∑' K : ↥(K0ᶜ : Set ReductionData), (deltaP p (K : ReductionData)).toReal from by
    linarith]
  exact (one_sub_add_mul_le (tsum_compl_K0_toReal_le_nine_div_sq p) hD hM).trans_eq (by ring)

/-- There are constants `C > 0` and `p₀` such that, for every finite `Λ ⊆ 𝒦 ∖ 𝒦₀`, every finite set
of primes `Π`, every parameter tuple `(s, u, w, 𝐳, 𝐮)` with `Re(s) ≥ 0`, `‖u‖ ≤ 1`, `‖w‖ ≤ 1`,
`‖z_ℓ‖ ≤ 1` and `‖u_K‖ ≤ 1`, and every `M ≥ 1` bounding `Φ` uniformly over `𝒦`,

  `‖β_q + ∑_{K ∈ 𝒦 ∖ 𝒦₀} δ_q(K) Φ(K; s, u, w, 𝐳, 𝐮)‖ ≤ 1 + C·M/q²`

for every prime `q ≥ p₀`. -/
@[bsd_tamagawa "T023c"]
theorem exists_bounded_localFactor_bound :
    ∃ C : ℝ, ∃ p₀ : ℕ, 0 < C ∧
      ∀ (Λ : Finset ReductionData), Admissible Λ → ∀ (P : Finset ℕ) (s u w : ℂ) (z : P → ℂ)
        (uΛ : Λ → ℂ), 0 ≤ s.re → ‖u‖ ≤ 1 → ‖w‖ ≤ 1 → (∀ ℓ : P, ‖z ℓ‖ ≤ 1) →
        (∀ K : Λ, ‖uΛ K‖ ≤ 1) → ∀ M : ℝ, 1 ≤ M →
          (∀ K : ReductionData, ‖localWeight Λ P K s u w z uΛ‖ ≤ M) →
          ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q →
            ‖((β q).toReal : ℂ) + ∑' K : ↥(K0ᶜ : Set ReductionData),
                ((deltaP q (K : ReductionData)).toReal : ℂ)
                  * localWeight Λ P (K : ReductionData) s u w z uΛ‖
              ≤ 1 + C * M / (q : ℝ) ^ 2 :=
  ⟨9, 2, by norm_num, fun _ _ _ s u w z uΛ _ _ _ _ _ _ hM hbdd q _ _ =>
    norm_localFactor_le_one_add_nine_mul_div_sq q s u w z uΛ hM hbdd⟩

end WeierstrassCurve
