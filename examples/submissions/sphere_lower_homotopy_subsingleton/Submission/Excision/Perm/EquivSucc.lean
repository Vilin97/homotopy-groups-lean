/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.ZMod.IntUnitsPower

/-!
# Permutations

-/

@[expose] public section

@[simp]
lemma Fin.succAbove_le_iff {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i ≤ p ↔ i.castSucc < p := by
  by_cases! hp : i.castSucc < p
  · rw [succAbove_of_castSucc_lt _ _ hp]
    have := hp.le
    tauto
  · rw [succAbove_of_le_castSucc _ _ hp, castSucc_lt_iff_succ_le]

namespace Equiv.Perm

variable {n : ℕ}

/-- Given `i : Fin (n + 2)` and `σ : Perm (Fin (n + 1)`, this is the permutation
of `Fin (n + 2)` which sends `0` to `i` and `j.succ` to `i.succAbove (σ j)`. -/
noncomputable def equivSuccSymm (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    Perm (Fin (n + 2)) :=
  Equiv.ofBijective
    (Fin.cases i (Fin.succAbove i ∘ σ)) (by
      rw [Nat.bijective_iff_injective_and_card]
      refine ⟨fun j k h ↦ ?_, rfl⟩
      obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;>
        obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_eq_succ <;> aesop)

@[simp]
lemma equivSuccSymm_zero (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    equivSuccSymm i σ 0 = i := rfl

@[simp]
lemma equivSuccSymm_succ (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    equivSuccSymm i σ j.succ = i.succAbove (σ j) := rfl

@[simp]
lemma equivSuccSymm_symm_eq_zero (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    (equivSuccSymm i σ).symm i = 0 :=
  (equivSuccSymm i σ).injective (by simp)

@[simp]
lemma equivSuccSymm_symm_succAbove (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    (equivSuccSymm i σ).symm (i.succAbove (σ j)) = j.succ :=
  (equivSuccSymm i σ).injective (by simp)

variable (n) in
lemma equivSuccSymm_uncurry_bijective : Function.Bijective (equivSuccSymm (n := n)).uncurry := by
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨fun ⟨i, σ⟩ ⟨i', σ'⟩ h ↦ ?_, ?_⟩
  · obtain rfl : i = i' := by simpa using DFunLike.congr_fun h 0
    obtain rfl : σ = σ' := by
      ext j : 1
      simpa using DFunLike.congr_fun h j.succ
    rfl
  · rw [Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin,
      Nat.factorial_succ (n + 1)]

/-- A bijection between `Perm (Fin (n + 2))` and `Fin (n + 2) × Perm (Fin (n + 1))`.
See `equivSuccSymm` for the definition of the inverse map. -/
noncomputable def equivSucc : Perm (Fin (n + 2)) ≃ Fin (n + 2) × Perm (Fin (n + 1)) :=
  (Equiv.ofBijective _ (equivSuccSymm_uncurry_bijective n)).symm

@[simp]
lemma equivSucc_symm (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    equivSucc.symm ⟨i, σ⟩ = equivSuccSymm i σ := rfl

@[simp]
lemma sign_equivSuccSymm (i : Fin (n + 2)) (σ : Perm (Fin (n + 1))) :
    (equivSuccSymm i σ).sign = (-1) ^ i.val * σ.sign := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi, Fin.prod_univ_succ]
  congr
  · let S : Finset (Fin (n + 1)) := { x | i.succAbove (σ x) ≤ i }
    have : S = Finset.image σ.symm { x | x.castSucc < i } := by aesop
    have hS : S.card = i.val := by
      simp only [this, Finset.card_image_of_injective _ (Equiv.injective _)]
      exact Finset.card_eq_of_bijective (fun j hj ↦ ⟨j, by grind⟩) (by grind) (by grind) (by simp)
    trans ∏ j ∈ S, -1
    · simp only [Fin.Ioi_zero_eq_map, equivSuccSymm_zero, Finset.prod_map, Fin.coe_succEmb,
        equivSuccSymm_succ, ← S.prod_mul_prod_compl, Finset.prod_const]
      trans ((-1 : ℤˣ) ^ S.card) * 1
      · congr 1
        · trans ∏ i ∈ S, -1
          · exact Finset.prod_congr rfl (by simp [S])
          · simp
            rfl
        · simp [Finset.prod_eq_one, S]
      · exact mul_one _
    · simp [hS]
      rfl
  · simp [Equiv.Perm.sign_eq_prod_prod_Ioi]

end Equiv.Perm
