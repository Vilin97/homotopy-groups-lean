/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# ...

-/

@[expose] public section

lemma Finsupp.sum_finsetSum
    {ι α M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (f : ι → (α →₀ M)) (s : Finset ι) (g : α → M → N)
    (h₁ : ∀ a, g a 0 = 0)
    (h₂ : ∀ a m₁ m₂, g a (m₁ + m₂) = g a m₁ + g a m₂) :
    (∑ i ∈ s, f i).sum g = ∑ i ∈ s, (f i).sum g :=
  map_sum (liftAddHom (fun a ↦ { toFun := g a, map_zero' := h₁ a, map_add' := h₂ a })) f s

lemma Finsupp.rec' {α M : Type*} [AddCommMonoid M]
    {motive : (α →₀ M) → Prop}
    (sum : ∀ (n : ℕ) (a : Fin n → α) (m : Fin n → M) (_ : Function.Injective a)
      (_ : ∀ a, m a ≠ 0),
      motive (∑ (i : Fin n), .single (a i) (m i)))
    (f : α →₀ M) :
    motive f := by
  convert sum f.support.card (fun i ↦ f.support.equivFin.symm i)
    (fun i ↦ f (f.support.equivFin.symm i))
      (Subtype.val_injective.comp f.support.equivFin.symm.injective) (by grind)
  ext j
  simp only [coe_finsetSum, Finset.sum_apply]
  by_cases hj : j ∈ f.support
  · rw [Finset.sum_eq_single (f.support.equivFin ⟨j, hj⟩) (fun k _ hk ↦ ?_) (by simp),
      Equiv.symm_apply_apply, single_eq_same]
    rw [single_apply_eq_zero]
    rintro rfl
    simp at hk
  · rw [notMem_support_iff] at hj
    rw [hj]
    refine (Finset.sum_eq_zero (fun i _ ↦ ?_)).symm
    rw [single_apply_eq_zero]
    intro hj'
    rwa [← hj']
