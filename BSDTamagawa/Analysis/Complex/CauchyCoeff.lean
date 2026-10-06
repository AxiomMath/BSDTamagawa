/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guillaume Remy, Ashvin A. Swaminathan
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import BSDTamagawa.Attr

/-!
# Cauchy coefficient extraction

Uniform convergence on circles (resp. polytori) forces convergence of the individual power-series
coefficients: a family `G_X` of generating functions converging uniformly on the polytori of the
open unit polydisc has coefficients converging to those of the limit.

## Main definitions

* `HasPolydiscExpansion c f`: the multivariate power series with coefficient family
  `c : (ι →₀ ℕ) → ℂ` sums to `f` at every point of the open unit polydisc.
* `TendstoUniformlyOnPolytori G_seq G`: `G_seq X → G` uniformly on each polytorus
  `{z | ∀ i, ‖z i‖ = ρ i}` with `0 < ρ i < 1`.

## Main results

* `cauchy_coeff_convergence`: the one-variable statement.
* `cauchy_coeff_convergence_multivar`: the several-variable statement.
-/

@[expose] public section

open Complex Filter Metric Topology

/-- `f` is the sum of the multivariate power series with coefficients `c` on the open unit polydisc
`{z | ∀ i, ‖z i‖ < 1}`. -/
def HasPolydiscExpansion {ι : Type*} [Fintype ι] (c : (ι →₀ ℕ) → ℂ)
    (f : (ι → ℂ) → ℂ) : Prop :=
  ∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) → HasSum (fun j : ι →₀ ℕ => c j • ∏ i, z i ^ (j i)) (f z)

/-- `G_seq → G` uniformly on every polytorus `{z | ∀ i, ‖z i‖ = ρ i}` of radii `ρ` with
`0 < ρ i < 1`. -/
def TendstoUniformlyOnPolytori {ι : Type*} (G_seq : ℕ → (ι → ℂ) → ℂ)
    (G : (ι → ℂ) → ℂ) : Prop :=
  ∀ ρ : ι → ℝ, (∀ i, 0 < ρ i) → (∀ i, ρ i < 1) →
    TendstoUniformlyOn G_seq G atTop {z : ι → ℂ | ∀ i, ‖z i‖ = ρ i}

/-- The conclusion of `cauchy_coeff_convergence_multivar`, as a property of the index type `ι`
alone. -/
private def CauchyCoeffConv (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (G_seq : ℕ → (ι → ℂ) → ℂ) (β : ℕ → (ι →₀ ℕ) → ℂ) (G : (ι → ℂ) → ℂ)
    (β_lim : (ι →₀ ℕ) → ℂ),
    (∀ X, HasPolydiscExpansion (β X) (G_seq X)) → HasPolydiscExpansion β_lim G →
    TendstoUniformlyOnPolytori G_seq G →
    ∀ j, Tendsto (β · j) atTop (𝓝 (β_lim j))

/-! ## One variable: Cauchy's formula for the coefficients -/

/-- A function with a power series on the open unit ball is differentiable on every closed ball of
radius `ρ < 1`. -/
private lemma differentiableOn_closedBall_of_hasFPowerSeriesOnBall
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesOnBall f p 0 1) {ρ : ℝ} (hρ_lt : ρ < 1) :
    DifferentiableOn ℂ f (Metric.closedBall 0 ρ) := by
  refine hf.differentiableOn.mono fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  rw [Metric.mem_eball, edist_zero_right, show (1 : ENNReal) = ↑(1 : NNReal) from rfl,
    enorm_lt_coe]
  exact_mod_cast hz.trans_lt hρ_lt

/-- The scalar power series of `f` at `0` is the Cauchy power series computed on any circle of
radius `ρ ∈ (0, 1)`: a function has at most one power series expansion at a point. -/
private lemma ofScalars_eq_cauchyPowerSeries
    {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) 0 1)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) :
    FormalMultilinearSeries.ofScalars ℂ c = cauchyPowerSeries f 0 ρ :=
  hf.hasFPowerSeriesAt.eq_formalMultilinearSeries
    ((differentiableOn_closedBall_of_hasFPowerSeriesOnBall hf hρ_lt).hasFPowerSeriesOnBall
      (show (0 : NNReal) < ⟨ρ, hρ_pos.le⟩ from hρ_pos)).hasFPowerSeriesAt

/-- **Cauchy's formula for the coefficients.** The `n`-th coefficient of `f` is the contour
integral `(2πi)⁻¹ ∮_{|z| = ρ} z⁻ⁿ⁻¹ f z`, for any radius `ρ ∈ (0, 1)`. -/
private lemma coeff_eq_cauchy_integral
    {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) 0 1)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) (n : ℕ) :
    c n = (2 * ↑Real.pi * I)⁻¹ •
      ∮ z in C(0, ρ), (1 / (z - 0)) ^ n • (z - 0)⁻¹ • f z := by
  have h1 : (FormalMultilinearSeries.ofScalars ℂ c n) (fun _ => (1 : ℂ)) = c n := by simp
  rw [← h1, ofScalars_eq_cauchyPowerSeries hf hρ_pos hρ_lt]
  exact cauchyPowerSeries_apply f 0 ρ n 1

/-- On the circle `{‖z‖ = ρ}`, the Cauchy integrands of `f` and `g` differ by at most
`ε · ρ⁻¹ ^ (n + 1)` once `f` and `g` differ by at most `ε` there. -/
private lemma integrand_norm_bound
    {f g : ℂ → ℂ} {ρ : ℝ} (hρ_pos : 0 < ρ) (n : ℕ)
    {ε : ℝ} (hbound : ∀ z : ℂ, ‖z‖ = ρ → ‖f z - g z‖ ≤ ε)
    {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) ρ) :
    ‖(1 / (z - 0)) ^ n • (z - 0)⁻¹ • f z -
     (1 / (z - 0)) ^ n • (z - 0)⁻¹ • g z‖ ≤ ε * ρ⁻¹ ^ (n + 1) := by
  simp only [sub_zero, ← smul_sub]
  rw [norm_smul, norm_smul, ← mul_assoc,
    show ‖(1 / z) ^ n‖ * ‖z⁻¹‖ = ρ⁻¹ ^ (n + 1) from by
      rw [one_div, norm_pow, norm_inv, mem_sphere_zero_iff_norm.mp hz, pow_succ],
    mul_comm]
  gcongr
  exact hbound z (mem_sphere_zero_iff_norm.mp hz)

/-- The Cauchy integrand `z ↦ z⁻ⁿ⁻¹ f z` is circle-integrable on `{‖z‖ = ρ}`: it is continuous
there, the pole at `0` being off the circle. -/
private lemma circleIntegrable_cauchy_integrand
    {f : ℂ → ℂ} {ρ : ℝ}
    (hf_diff : DifferentiableOn ℂ f (Metric.closedBall 0 ρ))
    (hρ_pos : 0 < ρ) (n : ℕ) :
    CircleIntegrable (fun z => (1 / (z - 0)) ^ n • (z - 0)⁻¹ • f z) 0 ρ := by
  apply ContinuousOn.circleIntegrable hρ_pos.le
  have hne : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, z - 0 ≠ 0 := fun z hz h => by
    simp [h] at hz; linarith
  exact ((continuousOn_const.div (continuousOn_id.sub continuousOn_const) hne).pow _).smul
    ((continuousOn_id.sub continuousOn_const).inv₀ hne |>.smul
      (hf_diff.mono Metric.sphere_subset_closedBall).continuousOn)

/-- The two Cauchy integrals differ by at most `(2πρ) · ε · ρ⁻¹ ^ (n + 1)`: the length of the
contour times the pointwise bound on the integrands. -/
private lemma norm_integral_diff_le
    {f g : ℂ → ℂ} {ρ : ℝ}
    (hf_diff : DifferentiableOn ℂ f (Metric.closedBall 0 ρ))
    (hg_diff : DifferentiableOn ℂ g (Metric.closedBall 0 ρ))
    (hρ_pos : 0 < ρ) (n : ℕ)
    {ε : ℝ}
    (hint_bound : ∀ z ∈ Metric.sphere (0 : ℂ) ρ,
      ‖(1 / (z - 0)) ^ n • (z - 0)⁻¹ • f z -
       (1 / (z - 0)) ^ n • (z - 0)⁻¹ • g z‖ ≤ ε * ρ⁻¹ ^ (n + 1)) :
    ‖(∮ z in C(0, ρ), (1 / (z - 0)) ^ n • (z - 0)⁻¹ • f z) -
     (∮ z in C(0, ρ), (1 / (z - 0)) ^ n • (z - 0)⁻¹ • g z)‖ ≤
    2 * Real.pi * ρ * (ε * ρ⁻¹ ^ (n + 1)) := by
  rw [← circleIntegral.integral_sub
    (circleIntegrable_cauchy_integrand hf_diff hρ_pos n)
    (circleIntegrable_cauchy_integrand hg_diff hρ_pos n)]
  exact circleIntegral.norm_integral_le_of_norm_le_const hρ_pos.le hint_bound

/-- Dividing the contour bound by `2πi` cancels the `2π` and one power of `ρ`, leaving the
coefficient bound `ε · ρ⁻¹ ^ n`. -/
private lemma cauchy_bound_simplify
    {ε ρ : ℝ} (hρ_pos : 0 < ρ) (n : ℕ)
    {I_val : ℂ}
    (hI : ‖I_val‖ ≤ 2 * Real.pi * ρ * (ε * ρ⁻¹ ^ (n + 1))) :
    ‖(2 * ↑Real.pi * I)⁻¹ • I_val‖ ≤ ε * ρ⁻¹ ^ n := by
  rw [norm_smul, show ‖(2 * ↑Real.pi * I)⁻¹‖ = (2 * Real.pi)⁻¹ from by
    simp [norm_inv, Complex.norm_I, Complex.norm_real, abs_of_pos Real.pi_pos, mul_comm]]
  calc (2 * Real.pi)⁻¹ * ‖I_val‖
      _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * ρ * (ε * ρ⁻¹ ^ (n + 1))) := by gcongr
      _ = ε * ρ⁻¹ ^ n := by rw [pow_succ]; field_simp

/-- **The coefficient estimate.** If `f` and `g` have power series on the open unit disc and differ
by at most `ε` on the circle of radius `ρ ∈ (0, 1)`, then their `n`-th coefficients differ by at
most `ε · ρ⁻¹ ^ n`. -/
private lemma coeff_diff_le_of_norm_le
    {f g : ℂ → ℂ} {cf cg : ℕ → ℂ}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ cf) 0 1)
    (hg : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℂ cg) 0 1)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) (n : ℕ)
    {ε : ℝ} (hbound : ∀ z : ℂ, ‖z‖ = ρ → ‖f z - g z‖ ≤ ε) :
    ‖cf n - cg n‖ ≤ ε * ρ⁻¹ ^ n := by
  rw [coeff_eq_cauchy_integral hf hρ_pos hρ_lt n,
    coeff_eq_cauchy_integral hg hρ_pos hρ_lt n, ← smul_sub]
  exact cauchy_bound_simplify hρ_pos n
    (norm_integral_diff_le
      (differentiableOn_closedBall_of_hasFPowerSeriesOnBall hf hρ_lt)
      (differentiableOn_closedBall_of_hasFPowerSeriesOnBall hg hρ_lt)
      hρ_pos n (fun z hz => integrand_norm_bound hρ_pos n hbound hz))

/-- Uniform convergence on the circle `{‖z‖ = ρ}` gives, eventually in `X`, the uniform `ε`-bound
on `‖F X z - G z‖`. -/
private lemma uniform_conv_gives_bound
    {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {ρ : ℝ}
    (hconv : TendstoUniformlyOn F G atTop {u : ℂ | ‖u‖ = ρ})
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, ∀ z : ℂ, ‖z‖ = ρ → ‖F X z - G z‖ ≤ ε := by
  refine (Metric.tendstoUniformlyOn_iff.mp hconv ε hε).mono fun X hX z hz => ?_
  rw [← dist_eq_norm, dist_comm]
  exact (hX z hz).le

/-- Cauchy coefficient convergence (one variable). Let `F X` be a sequence of functions with power
series `∑ m, a X m * u^m` on the open unit disc, converging uniformly to `G` (with coefficients
`b`) on every circle `{‖u‖ = ρ}`, `0 < ρ < 1`. Then for each fixed `n`, `a X n → b n` as
`X → ∞`. -/
@[bsd_tamagawa "T039"]
theorem cauchy_coeff_convergence
    (F : ℕ → ℂ → ℂ) (a : ℕ → ℕ → ℂ) (G : ℂ → ℂ) (b : ℕ → ℂ)
    (hF : ∀ X, HasFPowerSeriesOnBall (F X) (FormalMultilinearSeries.ofScalars ℂ (a X)) 0 1)
    (hG : HasFPowerSeriesOnBall G (FormalMultilinearSeries.ofScalars ℂ b) 0 1)
    (hconv : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
        TendstoUniformlyOn F G atTop {u : ℂ | ‖u‖ = ρ})
    (n : ℕ) :
    Tendsto (fun X => a X n) atTop (𝓝 (b n)) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_pos_mul_lt hε (((1 : ℝ) / 2)⁻¹ ^ n)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (uniform_conv_gives_bound
    (hconv (1/2) (by norm_num) (by norm_num)) hδ_pos)
  refine ⟨N, fun X hX => ?_⟩
  rw [Complex.dist_eq]
  exact lt_of_le_of_lt (coeff_diff_le_of_norm_le (hF X) hG
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1:ℝ)/2 < 1) n (hN X hX))
    ((mul_comm _ _).trans_lt hδ)

/-! ## Several variables: transport along an equivalence of index types -/

/-- Reindexing a monomial along `e : β ≃ α` leaves it unchanged. -/
private lemma prod_reindex_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : β ≃ α) (w : α → ℂ) (k : α →₀ ℕ) :
    ∏ i : β, (w ∘ e) i ^ (((Finsupp.equivCongrLeft e).symm k) i) = ∏ i : α, w i ^ (k i) :=
  Fintype.prod_equiv e _ _ (congrFun rfl)

/-- A polydisc expansion in the variables `β` becomes one in the variables `α` after reindexing
both the variables and the multi-indices along `e : β ≃ α`. -/
private lemma hasSum_transport_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : β ≃ α)
    (c : (β →₀ ℕ) → ℂ) (w : α → ℂ) (s : ℂ)
    (h : HasSum (fun j : β →₀ ℕ => c j • ∏ i : β, (w ∘ e) i ^ (j i)) s) :
    HasSum (fun k : α →₀ ℕ => c ((Finsupp.equivCongrLeft e).symm k) •
      ∏ i : α, w i ^ (k i)) s := by
  refine ((Equiv.hasSum_iff (Finsupp.equivCongrLeft e).symm).mpr h).congr_fun fun k => ?_
  exact congrArg (c ((Finsupp.equivCongrLeft e).symm k) • ·) (prod_reindex_equiv e w k).symm

/-- Reindexing along `e : β ≃ α` pulls the polytorus of radii `ρ ∘ e` back to the polytorus of
radii `ρ`. -/
private lemma preimage_comp_equiv_eq {α β : Type*} (e : β ≃ α) (ρ : α → ℝ) :
    (fun w : α → ℂ => w ∘ e) ⁻¹' {z : β → ℂ | ∀ i, ‖z i‖ = ρ (e i)} =
      {w : α → ℂ | ∀ i, ‖w i‖ = ρ i} := by
  ext w
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Function.comp]
  exact ⟨fun h i => by obtain ⟨j, rfl⟩ := e.surjective i; exact h j, fun h i => h (e i)⟩

/-- Uniform convergence on a polytorus transports along reindexing, by `preimage_comp_equiv_eq`. -/
private lemma tendstoUniformlyOn_transport_equiv {α β : Type*} (e : β ≃ α)
    (G_seq : ℕ → (β → ℂ) → ℂ) (G : (β → ℂ) → ℂ) (ρ : α → ℝ)
    (h : TendstoUniformlyOn G_seq G atTop {z : β → ℂ | ∀ i, ‖z i‖ = ρ (e i)}) :
    TendstoUniformlyOn (fun X w => G_seq X (w ∘ e)) (fun w => G (w ∘ e)) atTop
      {w : α → ℂ | ∀ i, ‖w i‖ = ρ i} :=
  preimage_comp_equiv_eq e ρ ▸ h.comp (fun w : α → ℂ => w ∘ e)

/-- `CauchyCoeffConv` transports along an equivalence of index types. -/
private lemma cauchy_coeff_multivar_equiv
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : β ≃ α) (h_α : CauchyCoeffConv α) : CauchyCoeffConv β := by
  intro G_seq β_coeff G β_lim h_seq h_lim h_unif j
  set eF : (β →₀ ℕ) ≃ (α →₀ ℕ) := Finsupp.equivCongrLeft e
  have h_result := h_α
    (fun X w => G_seq X (w ∘ e))
    (fun X k => β_coeff X (eF.symm k))
    (fun w => G (w ∘ e))
    (fun k => β_lim (eF.symm k))
    ?_ ?_ ?_ (eF j)
  · simpa only [Equiv.symm_apply_apply] using h_result
  · intro X w hw
    exact hasSum_transport_equiv e (β_coeff X) w (G_seq X (w ∘ e))
      (h_seq X (w ∘ e) (fun i => hw (e i)))
  · intro w hw
    exact hasSum_transport_equiv e β_lim w (G (w ∘ e))
      (h_lim (w ∘ e) (fun i => hw (e i)))
  · intro ρ hpos hlt
    exact tendstoUniformlyOn_transport_equiv e G_seq G ρ
      (h_unif (ρ ∘ e) (fun i => hpos (e i)) (fun i => hlt (e i)))

/-! ## Several variables: the base case `PEmpty` -/

/-- With no variables the polydisc expansion has a single term, so the function is the constant
`c 0`. -/
private lemma hasSum_pempty_eq (c : (PEmpty →₀ ℕ) → ℂ) (f : (PEmpty → ℂ) → ℂ)
    (z : PEmpty → ℂ)
    (hf : HasSum (fun j : PEmpty →₀ ℕ => c j • ∏ i : PEmpty, z i ^ (j i)) (f z)) :
    f z = c 0 := by
  rw [← hf.tsum_eq]
  simp [tsum_fintype]

/-- **Base case.** With no variables the sole coefficient is the value of the function at the sole
point, and the hypotheses give convergence of those values. -/
private lemma cauchy_coeff_multivar_pempty : CauchyCoeffConv PEmpty := by
  intro G_seq β G β_lim hG_seq hG hconv j
  rw [Unique.eq_default j]
  let z₀ : PEmpty → ℂ := fun i => i.elim
  have hz₀ : ∀ i : PEmpty, ‖z₀ i‖ < 1 := fun i => i.elim
  have hpt := (hconv (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)).tendsto_at
    (x := z₀) fun i => i.elim
  rw [hasSum_pempty_eq β_lim G z₀ (hG z₀ hz₀)] at hpt
  exact hpt.congr fun X => hasSum_pempty_eq (β X) (G_seq X) z₀ (hG_seq X z₀ hz₀)

/-! ## Several variables: the inductive step `α ↝ Option α` -/

/-- The monomial attached to the multi-index `(n, j')` in the variables `Option α` splits as
`w ^ n` times the monomial of `j'` in the variables `α`. -/
private lemma prod_optionEquiv_symm_eq
    {α : Type*} [Fintype α]
    (z' : α → ℂ) (w : ℂ) (n : ℕ) (j' : α →₀ ℕ) :
    (∏ i : Option α, (fun i => Option.rec w z' i) i ^
      ((Finsupp.optionEquiv (α := α) (M := ℕ)).symm (n, j') i)) =
    w ^ n * ∏ a : α, z' a ^ (j' a) := by
  classical
  simp only [Finsupp.optionEquiv_symm_apply, Finsupp.coe_update, Fintype.prod_option,
    Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne,
    Finsupp.embDomain_some_some]

/-- The polydisc expansion in the variables `Option α`, reindexed over `ℕ × (α →₀ ℕ)` and with the
new variable `w` split off as the factor `w ^ p.1`. -/
private lemma hasSum_reindexed
    {α : Type*} [Fintype α]
    (c : (Option α →₀ ℕ) → ℂ)
    (f : (Option α → ℂ) → ℂ)
    (hf : HasPolydiscExpansion c f)
    (z' : α → ℂ) (hz' : ∀ i, ‖z' i‖ < 1)
    (w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (fun p : ℕ × (α →₀ ℕ) =>
      (c (Finsupp.optionEquiv.symm p) • ∏ a : α, z' a ^ (p.2 a)) * w ^ p.1)
      (f (fun i => Option.rec w z' i)) := by
  have hz : ∀ i : Option α, ‖(fun i => Option.rec w z' i : Option α → ℂ) i‖ < 1 :=
    fun i => by
      cases i with | none => exact hw | some a => exact hz' a
  refine ((Equiv.hasSum_iff Finsupp.optionEquiv.symm).mpr (hf _ hz)).congr_fun fun p => ?_
  obtain ⟨n, j'⟩ := p
  simp only [Function.comp, smul_eq_mul]
  rw [prod_optionEquiv_symm_eq z' w n j']
  ring

/-- **The slice coefficients converge.** For fixed `n`, the `α`-series obtained by freezing the
exponent of the new variable at `n` is summable on the open polydisc. -/
private lemma summable_reduced_coefficients
    {α : Type*} [Fintype α]
    (c : (Option α →₀ ℕ) → ℂ)
    (f : (Option α → ℂ) → ℂ)
    (hf : HasPolydiscExpansion c f)
    (n : ℕ) (z' : α → ℂ) (hz' : ∀ i, ‖z' i‖ < 1) :
    Summable (fun j' : α →₀ ℕ =>
      c (Finsupp.optionEquiv.symm (n, j')) • ∏ i : α, z' i ^ (j' i)) := by
  have hS := (hasSum_reindexed c f hf z' hz' (1/2) (by norm_num)).summable.prod_factor n
  dsimp only at hS
  rwa [summable_mul_right_iff (pow_ne_zero n (by norm_num : (1/2 : ℂ) ≠ 0))] at hS

/-- **The slice expansion.** For fixed `z'`, `w ↦ f (w, z')` is the one-variable power series whose
`n`-th coefficient is the sum of the coefficients with exponent `n` in the new variable. -/
private lemma hasSum_slice_ofScalars
    {α : Type*} [Fintype α]
    (c : (Option α →₀ ℕ) → ℂ)
    (f : (Option α → ℂ) → ℂ)
    (hf : HasPolydiscExpansion c f)
    (z' : α → ℂ) (hz' : ∀ i, ‖z' i‖ < 1)
    (w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (fun n => (∑' (j' : α →₀ ℕ),
        c (Finsupp.optionEquiv.symm (n, j')) • ∏ i : α, z' i ^ (j' i)) • w ^ n)
      (f (fun i => Option.rec w z' i)) := by
  have hfiber : ∀ n : ℕ, HasSum
      (fun j' : α →₀ ℕ =>
        (c (Finsupp.optionEquiv.symm (n, j')) • ∏ a : α, z' a ^ (j' a)) * w ^ n)
      ((∑' (j' : α →₀ ℕ),
        c (Finsupp.optionEquiv.symm (n, j')) • ∏ i : α, z' i ^ (j' i)) * w ^ n) :=
    fun n => (summable_reduced_coefficients c f hf n z' hz').hasSum.mul_right (w ^ n)
  exact (hasSum_reindexed c f hf z' hz' w hw).prod_fiberwise hfiber

/-- The slice power series converges absolutely at every real radius `r < 1`. -/
private lemma ofScalars_summable_norm_mul_pow
    {α : Type*} [Fintype α]
    (c : (Option α →₀ ℕ) → ℂ)
    (f : (Option α → ℂ) → ℂ)
    (hf : HasPolydiscExpansion c f)
    (z' : α → ℂ) (hz' : ∀ i, ‖z' i‖ < 1)
    (r : NNReal) (hr : (r : ℝ) < 1) :
    Summable (fun n => ‖(FormalMultilinearSeries.ofScalars ℂ
        (fun m => ∑' (j' : α →₀ ℕ),
           c (Finsupp.optionEquiv.symm (m, j')) • ∏ i : α, z' i ^ (j' i))) n‖ *
             (r : ℝ) ^ n) := by
  set a := fun m => ∑' (j' : α →₀ ℕ),
    c (Finsupp.optionEquiv.symm (m, j')) • ∏ i : α, z' i ^ (j' i)
  have h_norm := (hasSum_slice_ofScalars c f hf z' hz' (↑r : ℂ) (by
    rw [Complex.norm_real, Real.norm_of_nonneg r.coe_nonneg]; exact hr)).summable.norm
  simpa only [FormalMultilinearSeries.ofScalars_norm ℂ a, norm_smul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg r.coe_nonneg] using h_norm

/-- The slice power series has radius of convergence at least `1`. -/
private lemma ofScalars_radius_ge_one
    {α : Type*} [Fintype α]
    (c : (Option α →₀ ℕ) → ℂ)
    (f : (Option α → ℂ) → ℂ)
    (hf : HasPolydiscExpansion c f)
    (z' : α → ℂ) (hz' : ∀ i, ‖z' i‖ < 1) :
    (1 : ENNReal) ≤
      (FormalMultilinearSeries.ofScalars ℂ
        (fun m => ∑' (j' : α →₀ ℕ),
          c (Finsupp.optionEquiv.symm (m, j')) • ∏ i : α, z' i ^ (j' i))).radius :=
  ENNReal.le_of_forall_nnreal_lt fun r hr =>
    FormalMultilinearSeries.le_radius_of_summable _
      (ofScalars_summable_norm_mul_pow c f hf z' hz' r
        (by exact_mod_cast ENNReal.coe_lt_one_iff.mp hr))

/-- **The slice is a one-variable power series on the unit disc.** For every fixed `z'` in the open
polydisc, `w ↦ f (w, z')` has the slice power series on the open unit ball. -/
private lemma hasFPowerSeriesOnBall_of_option_hasSum
    {α : Type*} [Fintype α]
    (c : (Option α →₀ ℕ) → ℂ)
    (f : (Option α → ℂ) → ℂ)
    (hf : HasPolydiscExpansion c f)
    (z' : α → ℂ) (hz' : ∀ i, ‖z' i‖ < 1) :
    HasFPowerSeriesOnBall
      (fun w => f (fun i => Option.rec w z' i))
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => ∑' (j' : α →₀ ℕ),
          c (Finsupp.optionEquiv.symm (n, j')) • ∏ i : α, z' i ^ (j' i)))
      0 1 := by
  refine HasFPowerSeriesOnBall.mk (ofScalars_radius_ge_one c f hf z' hz') one_pos fun {y} hy => ?_
  simp only [zero_add, mem_eball, edist_zero_right] at hy ⊢
  rw [FormalMultilinearSeries.ofScalars_apply_eq']
  exact hasSum_slice_ofScalars c f hf z' hz' y
    (by exact_mod_cast (show (↑‖y‖₊ : ENNReal) < 1 from hy))

/-- **The slice coefficients converge uniformly in `z'`.** Uniform convergence on the polytorus of
radii `(r, ρ')` gives, eventually in `X`, the bound `ε · r⁻¹ ^ n` on the difference of the `n`-th
slice coefficients, uniformly over `z'` on the `α`-polytorus. -/
private lemma uniform_coeff_bound_of_polytorus_conv
    {α : Type*} [Fintype α]
    (G_seq : ℕ → (Option α → ℂ) → ℂ)
    (β_coeff : ℕ → (Option α →₀ ℕ) → ℂ)
    (G : (Option α → ℂ) → ℂ) (β_lim : (Option α →₀ ℕ) → ℂ)
    (hG_seq : ∀ X, HasPolydiscExpansion (β_coeff X) (G_seq X))
    (hG : HasPolydiscExpansion β_lim G)
    {r : ℝ} (hr_pos : 0 < r) (hr_lt : r < 1)
    {ρ' : α → ℝ} (hρ'_lt : ∀ i, ρ' i < 1)
    (hconv_poly : TendstoUniformlyOn G_seq G atTop
      {z : Option α → ℂ | ∀ i, ‖z i‖ = (fun i => Option.rec r ρ' i) i})
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X in atTop, ∀ z' : α → ℂ, (∀ i, ‖z' i‖ = ρ' i) →
      ‖(∑' (j' : α →₀ ℕ),
          β_coeff X (Finsupp.optionEquiv.symm (n, j')) • ∏ i : α, z' i ^ (j' i)) -
        (∑' (j' : α →₀ ℕ),
          β_lim (Finsupp.optionEquiv.symm (n, j')) • ∏ i : α, z' i ^ (j' i))‖ ≤
        ε * r⁻¹ ^ n := by
  refine (Metric.tendstoUniformlyOn_iff.mp hconv_poly ε hε).mono fun X hX z' hz' => ?_
  have hz'_lt : ∀ i, ‖z' i‖ < 1 := fun i => (hz' i).symm ▸ hρ'_lt i
  refine coeff_diff_le_of_norm_le
    (hasFPowerSeriesOnBall_of_option_hasSum (β_coeff X) (G_seq X) (hG_seq X) z' hz'_lt)
    (hasFPowerSeriesOnBall_of_option_hasSum β_lim G hG z' hz'_lt)
    hr_pos hr_lt n fun w hw => ?_
  rw [norm_sub_rev, ← dist_eq_norm]
  exact (hX (fun i => Option.rec w z' i)
    fun i => by cases i with | none => exact hw | some j => exact hz' j).le

/-- **The slice coefficients converge uniformly on polytori.** For each `n`, the `n`-th slice
coefficients converge uniformly on every polytorus in the `α`-variables. -/
private lemma coeff_tendstoUniformlyOn_of_option
    {α : Type*} [Fintype α]
    (G_seq : ℕ → (Option α → ℂ) → ℂ)
    (β_coeff : ℕ → (Option α →₀ ℕ) → ℂ)
    (G : (Option α → ℂ) → ℂ) (β_lim : (Option α →₀ ℕ) → ℂ)
    (hG_seq : ∀ X, HasPolydiscExpansion (β_coeff X) (G_seq X))
    (hG : HasPolydiscExpansion β_lim G)
    (hconv : TendstoUniformlyOnPolytori G_seq G) (n : ℕ) :
    TendstoUniformlyOnPolytori
      (fun X z' => ∑' (j' : α →₀ ℕ),
        β_coeff X (Finsupp.optionEquiv.symm (n, j')) • ∏ i : α, z' i ^ (j' i))
      (fun z' => ∑' (j' : α →₀ ℕ),
        β_lim (Finsupp.optionEquiv.symm (n, j')) • ∏ i : α, z' i ^ (j' i)) := by
  intro ρ' hρ'_pos hρ'_lt
  set r : ℝ := 1 / 2
  have hr_pos : (0 : ℝ) < r := by norm_num
  have hr_lt : r < 1 := by norm_num
  set ρ : Option α → ℝ := fun i => Option.rec r ρ' i
  have hρ_pos : ∀ i, 0 < ρ i := fun i => by cases i <;> simp_all [ρ, r]
  have hρ_lt : ∀ i, ρ i < 1 := fun i => by cases i <;> simp_all [ρ, r]
  refine Metric.tendstoUniformlyOn_iff.mpr fun δ hδ => ?_
  obtain ⟨ε, hε_pos, hε⟩ := exists_pos_mul_lt hδ (r⁻¹ ^ n)
  refine (uniform_coeff_bound_of_polytorus_conv G_seq β_coeff G β_lim hG_seq hG hr_pos hr_lt
    hρ'_lt (hconv ρ hρ_pos hρ_lt) n ε hε_pos).mono fun X hX z' hz' => ?_
  rw [dist_comm, dist_eq_norm]
  exact lt_of_le_of_lt (hX z' (Set.mem_ofPred.mp hz')) ((mul_comm _ _).trans_lt hε)

/-- **Inductive step.** `CauchyCoeffConv α` implies `CauchyCoeffConv (Option α)`. -/
private lemma cauchy_coeff_multivar_option
    {α : Type*} [Fintype α] [DecidableEq α] (h_α : CauchyCoeffConv α) :
    CauchyCoeffConv (Option α) := by
  intro G_seq β_coeff G β_lim hG_seq hG hconv j
  set n := j none
  set j' := j.some
  have hj : j = Finsupp.optionEquiv.symm (n, j') := by
    rw [Equiv.eq_symm_apply]; simp [n, j', Finsupp.optionEquiv_apply]
  rw [hj]
  apply h_α
      (fun X z' => ∑' (j'' : α →₀ ℕ),
        β_coeff X (Finsupp.optionEquiv.symm (n, j'')) • ∏ i : α, z' i ^ (j'' i))
      (fun X j'' => β_coeff X (Finsupp.optionEquiv.symm (n, j'')))
      (fun z' => ∑' (j'' : α →₀ ℕ),
        β_lim (Finsupp.optionEquiv.symm (n, j'')) • ∏ i : α, z' i ^ (j'' i))
      (fun j'' => β_lim (Finsupp.optionEquiv.symm (n, j'')))
  · intro X z' hz'
    exact (summable_reduced_coefficients (β_coeff X) (G_seq X) (hG_seq X) n z' hz').hasSum
  · intro z' hz'
    exact (summable_reduced_coefficients β_lim G hG n z' hz').hasSum
  · exact coeff_tendstoUniformlyOn_of_option G_seq β_coeff G β_lim hG_seq hG hconv n

/-! ## Several variables: the induction on `Fin n` -/

/-- `CauchyCoeffConv (Fin n)` holds for every `n`. -/
private lemma cauchy_coeff_multivar_fin (n : ℕ) : CauchyCoeffConv (Fin n) := by
  induction n with
  | zero =>
    exact cauchy_coeff_multivar_equiv (show Fin 0 ≃ PEmpty.{1} from Equiv.equivPEmpty (Fin 0))
      cauchy_coeff_multivar_pempty
  | succ n ih =>
    exact cauchy_coeff_multivar_equiv (finSuccEquiv n) (cauchy_coeff_multivar_option ih)

/-- Cauchy coefficient convergence (several variables). Let `ι` be a finite index type and
`G_seq X` a sequence of functions on the open polydisc with multi-index power series coefficients
`β X j`. If `G_seq X → G` uniformly on every polytorus `{z | ∀ i, ‖z i‖ = ρ i}` with `0 < ρ i < 1`,
then for each fixed multi-index `j : ι →₀ ℕ`, `β X j → β_lim j` as `X → ∞`. -/
@[bsd_tamagawa "T039"]
theorem cauchy_coeff_convergence_multivar
    {ι : Type*} [Fintype ι]
    (G_seq : ℕ → (ι → ℂ) → ℂ)
    (β : ℕ → (ι →₀ ℕ) → ℂ)
    (G : (ι → ℂ) → ℂ)
    (β_lim : (ι →₀ ℕ) → ℂ)
    (hG_seq : ∀ X, HasPolydiscExpansion (β X) (G_seq X))
    (hG : HasPolydiscExpansion β_lim G)
    (hconv : TendstoUniformlyOnPolytori G_seq G)
    (j : ι →₀ ℕ) :
    Tendsto (fun X => β X j) atTop (𝓝 (β_lim j)) := by
  classical
  exact cauchy_coeff_multivar_equiv (Fintype.equivFin ι)
    (cauchy_coeff_multivar_fin (Fintype.card ι))
    G_seq β G β_lim hG_seq hG hconv j
