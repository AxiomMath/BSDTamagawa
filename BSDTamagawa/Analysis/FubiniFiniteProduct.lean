/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Fubini for a finite product of absolutely convergent series

A finite product of absolutely convergent complex series expands as a single series over the
multi-indices:

`∏_{i ∈ I} (∑_{n ≥ 0} f_i(n)) = ∑_{𝐭 : I →₀ ℕ} ∏_{i ∈ I} f_i(𝐭 i)`,

for a *finite* index type `I`. The proof, by induction on `I`, also shows that the multi-index
series converges absolutely. This extends Mathlib's two-factor case
`tsum_mul_tsum_of_summable_norm`.

## Main results

* `BSDTamagawa.Analysis.FinsuppFubini.hasSum_finsuppProd`: the displayed identity, as a `HasSum`
  over `I →₀ ℕ`.
-/

@[expose] public section

namespace BSDTamagawa.Analysis.FinsuppFubini

/-- The two clauses of the Fubini statement (absolute convergence of the multi-index series and its
value), as a property of the finite index type alone. -/
private def FubiniProd (ι : Type*) [Fintype ι] : Prop :=
  ∀ f : ι → ℕ → ℂ, (∀ i, Summable fun t : ℕ => ‖f i t‖) →
    Summable (fun t : ι →₀ ℕ => ‖∏ i, f i (t i)‖) ∧
      HasSum (fun t : ι →₀ ℕ => ∏ i, f i (t i)) (∏ i, ∑' n : ℕ, f i n)

/-- `FubiniProd` transports along an equivalence of index types. -/
private lemma fubiniProd_of_equiv {α β : Type*} [Fintype α] [Fintype β] (e : β ≃ α)
    (h : FubiniProd α) : FubiniProd β := by
  intro f hf
  obtain ⟨hs, hsum⟩ := h (fun a => f (e.symm a)) fun a => hf (e.symm a)
  have hterm : ∀ t : β →₀ ℕ,
      (∏ a : α, f (e.symm a) ((Finsupp.equivCongrLeft e t) a)) = ∏ b : β, f b (t b) := by
    intro t
    refine Fintype.prod_equiv e.symm _ _ fun a => ?_
    simp [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_apply]
  have hval : (∏ a : α, ∑' n : ℕ, f (e.symm a) n) = ∏ b : β, ∑' n : ℕ, f b n :=
    Fintype.prod_equiv e.symm _ _ fun _ => rfl
  refine ⟨?_, ?_⟩
  · refine ((Equiv.summable_iff (Finsupp.equivCongrLeft e)).mpr hs).congr fun t => ?_
    rw [Function.comp_apply, hterm t]
  · rw [← hval]
    exact ((Equiv.hasSum_iff (Finsupp.equivCongrLeft e)).mpr hsum).congr_fun
      fun t => (hterm t).symm

/-- **Base case.** With no index there is a single multi-index and the product is empty, so both
sides are `1`. -/
private lemma fubiniProd_pempty : FubiniProd PEmpty := by
  intro f _
  have hall : ∀ t : PEmpty →₀ ℕ, t = 0 := fun t => Finsupp.ext fun a => a.elim
  refine ⟨(hasSum_single (0 : PEmpty →₀ ℕ)
    (f := fun t : PEmpty →₀ ℕ => ‖∏ i : PEmpty, f i (t i)‖)
    fun t ht => absurd (hall t) ht).summable, ?_⟩
  simp

/-- **Inductive step.** `FubiniProd α` implies `FubiniProd (Option α)`. -/
private lemma fubiniProd_option {α : Type*} [Fintype α] (h : FubiniProd α) :
    FubiniProd (Option α) := by
  intro f hf
  set g : α → ℕ → ℂ := fun a => f (Option.some a) with hg
  obtain ⟨hsA, hA⟩ := h g fun a => hf (Option.some a)
  have hnone : Summable fun n : ℕ => ‖f none n‖ := hf none
  have hmulnorm : Summable fun q : ℕ × (α →₀ ℕ) => ‖f none q.1 * ∏ a : α, g a (q.2 a)‖ :=
    Summable.mul_norm (f := fun n : ℕ => f none n)
      (g := fun j : α →₀ ℕ => ∏ a : α, g a (j a)) hnone hsA
  have hmul : HasSum (fun q : ℕ × (α →₀ ℕ) => f none q.1 * ∏ a : α, g a (q.2 a))
      ((∑' n : ℕ, f none n) * ∏ a : α, ∑' n : ℕ, g a n) := by
    rw [← hA.tsum_eq, tsum_mul_tsum_of_summable_norm (f := fun n : ℕ => f none n)
      (g := fun j : α →₀ ℕ => ∏ a : α, g a (j a)) hnone hsA]
    exact hmulnorm.of_norm.hasSum
  have hterm : ∀ t : Option α →₀ ℕ,
      (∏ i : Option α, f i (t i))
        = f none ((Finsupp.optionEquiv t).1) * ∏ a : α, g a ((Finsupp.optionEquiv t).2 a) := by
    intro t
    rw [Fintype.prod_option (fun i : Option α => f i (t i))]
    simp only [hg, Finsupp.optionEquiv_apply, Finsupp.some_apply]
  refine ⟨?_, ?_⟩
  · refine ((Equiv.summable_iff (Finsupp.optionEquiv (α := α) (M := ℕ))).mpr
      hmulnorm).congr fun t => ?_
    rw [Function.comp_apply, ← hterm t]
  · rw [Fintype.prod_option (fun i : Option α => ∑' n : ℕ, f i n)]
    exact ((Equiv.hasSum_iff (Finsupp.optionEquiv (α := α) (M := ℕ))).mpr hmul).congr_fun hterm

/-- `FubiniProd (Fin n)` holds for every `n`. -/
private lemma fubiniProd_fin (n : ℕ) : FubiniProd (Fin n) := by
  induction n with
  | zero =>
    exact fubiniProd_of_equiv (show Fin 0 ≃ PEmpty.{1} from Equiv.equivPEmpty (Fin 0))
      fubiniProd_pempty
  | succ n ih => exact fubiniProd_of_equiv (finSuccEquiv n) (fubiniProd_option ih)

/-- **Fubini for a finite product of absolutely convergent series.** For a finite index type `ι`
and complex families `(f i)` each absolutely summable,

`∑_{𝐭 : ι →₀ ℕ} ∏_{i} f_i(𝐭 i) = ∏_{i} (∑_{n ≥ 0} f_i(n))`. -/
theorem hasSum_finsuppProd {ι : Type*} [Fintype ι] (f : ι → ℕ → ℂ)
    (hf : ∀ i, Summable fun t : ℕ => ‖f i t‖) :
    HasSum (fun t : ι →₀ ℕ => ∏ i, f i (t i)) (∏ i, ∑' n : ℕ, f i n) :=
  (fubiniProd_of_equiv (Fintype.equivFin ι) (fubiniProd_fin (Fintype.card ι)) f hf).2

end BSDTamagawa.Analysis.FinsuppFubini
