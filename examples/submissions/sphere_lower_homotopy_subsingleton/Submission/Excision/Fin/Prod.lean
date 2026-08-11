/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# ...

-/

@[to_additive]
public lemma Fin.prod_univ_eq_prod_of_le
    {α : Type*} [CommMonoid α] {n : ℕ} (f : Fin n → α) (k : ℕ) (hk : k ≤ n) :
    ∏ i, f i = (∏ (i : Fin k), f (i.castLE hk)) *
      ∏ (i : Fin n) with k ≤ i.val, f i := by
  let s : Finset (Fin n) := { i | k ≤ i.val }
  have : sᶜ = ({ i | i.val < k } : Finset (Fin n)) := by aesop
  rw [← s.prod_compl_mul_prod, this]
  congr 1
  apply Finset.prod_bij' (fun i hi ↦ ⟨i.val, by simpa using hi⟩)
    (fun i hi ↦ i.castLE hk)
  all_goals simp
