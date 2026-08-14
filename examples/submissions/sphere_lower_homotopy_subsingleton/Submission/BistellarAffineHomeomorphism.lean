/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.Order.Lattice

/-!
# A boundary-fixed affine homeomorphism for a bistellar move

For finite nonempty vertex types `α` and `β`, the two local bistellar balls have affine models

* `Δ α * ∂Δ β`: some right barycentric coordinate vanishes;
* `∂Δ α * Δ β`: some left barycentric coordinate vanishes.

This file gives an explicit homeomorphism between these models.  Given a point in the first ball,
subtract its least left coordinate from every left coordinate and redistribute the removed mass
uniformly over the right coordinates.  The inverse performs the symmetric operation.  On the
common boundary, where a coordinate on each side vanishes, the least left coordinate is zero, so
the homeomorphism is literally the identity.

This is the local piece required by the pushout gluing interface in
`Submission.BistellarMoveDecomposition`; the remaining comparison is to identify ordered
simplicial-set realizations with these affine carriers.

## Main results

* `Submission.FiniteOrderedComplex.affineBistellarHomeomorph`: the explicit homeomorphism of
  affine local bistellar balls;
* `Submission.FiniteOrderedComplex.affineBistellarHomeomorph_fixed_of_left_zero`: it fixes the
  common boundary pointwise.
-/

noncomputable section

open scoped BigOperators

namespace Submission.FiniteOrderedComplex

variable (α β : Type*) [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]

/-- The affine carrier of `Δ α * ∂Δ β`. -/
abbrev affineBistellarOld : Type _ :=
  {x : stdSimplex ℝ (α ⊕ β) // ∃ b : β, x (Sum.inr b) = 0}

/-- The affine carrier of `∂Δ α * Δ β`. -/
abbrev affineBistellarNew : Type _ :=
  {x : stdSimplex ℝ (α ⊕ β) // ∃ a : α, x (Sum.inl a) = 0}

/-- The least left barycentric coordinate. -/
def affineBistellarLeftMin (x : stdSimplex ℝ (α ⊕ β)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun a : α ↦ x (Sum.inl a)

/-- The least right barycentric coordinate. -/
def affineBistellarRightMin (x : stdSimplex ℝ (α ⊕ β)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun b : β ↦ x (Sum.inr b)

omit [Nonempty β] in
/-- The least left coordinate is no greater than every left coordinate. -/
theorem affineBistellarLeftMin_le (x : stdSimplex ℝ (α ⊕ β)) (a : α) :
    affineBistellarLeftMin α β x ≤ x (Sum.inl a) := by
  exact Finset.inf'_le _ (Finset.mem_univ a)

omit [Nonempty α] in
/-- The least right coordinate is no greater than every right coordinate. -/
theorem affineBistellarRightMin_le (x : stdSimplex ℝ (α ⊕ β)) (b : β) :
    affineBistellarRightMin α β x ≤ x (Sum.inr b) := by
  exact Finset.inf'_le _ (Finset.mem_univ b)

omit [Nonempty β] in
/-- The least left barycentric coordinate is nonnegative. -/
theorem affineBistellarLeftMin_nonneg (x : stdSimplex ℝ (α ⊕ β)) :
    0 ≤ affineBistellarLeftMin α β x := by
  apply Finset.le_inf'
  intro a ha
  exact x.2.1 _

omit [Nonempty α] in
/-- The least right barycentric coordinate is nonnegative. -/
theorem affineBistellarRightMin_nonneg (x : stdSimplex ℝ (α ⊕ β)) :
    0 ≤ affineBistellarRightMin α β x := by
  apply Finset.le_inf'
  intro b hb
  exact x.2.1 _

omit [Nonempty β] in
/-- The least left coordinate varies continuously. -/
theorem continuous_affineBistellarLeftMin :
    Continuous (affineBistellarLeftMin α β) := by
  apply Continuous.finset_inf'_apply Finset.univ_nonempty
  intro a ha
  exact (continuous_apply _).comp continuous_subtype_val

omit [Nonempty α] in
/-- The least right coordinate varies continuously. -/
theorem continuous_affineBistellarRightMin :
    Continuous (affineBistellarRightMin α β) := by
  apply Continuous.finset_inf'_apply Finset.univ_nonempty
  intro b hb
  exact (continuous_apply _).comp continuous_subtype_val

private theorem card_cast_ne_zero (γ : Type*) [Fintype γ] [Nonempty γ] :
    (Fintype.card γ : ℝ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

/-- Subtract the least left coordinate and redistribute its mass uniformly on the right. -/
def affineBistellarOldToNewFn (x : stdSimplex ℝ (α ⊕ β)) : α ⊕ β → ℝ
  | Sum.inl a => x (Sum.inl a) - affineBistellarLeftMin α β x
  | Sum.inr b => x (Sum.inr b) +
      (Fintype.card α : ℝ) / (Fintype.card β : ℝ) * affineBistellarLeftMin α β x

/-- Subtract the least right coordinate and redistribute its mass uniformly on the left. -/
def affineBistellarNewToOldFn (x : stdSimplex ℝ (α ⊕ β)) : α ⊕ β → ℝ
  | Sum.inl a => x (Sum.inl a) +
      (Fintype.card β : ℝ) / (Fintype.card α : ℝ) * affineBistellarRightMin α β x
  | Sum.inr b => x (Sum.inr b) - affineBistellarRightMin α β x

omit [Nonempty β] in
/-- The old-to-new coordinate formula is nonnegative. -/
theorem affineBistellarOldToNewFn_nonneg (x : stdSimplex ℝ (α ⊕ β)) (i : α ⊕ β) :
    0 ≤ affineBistellarOldToNewFn α β x i := by
  cases i with
  | inl a =>
      exact sub_nonneg.mpr (affineBistellarLeftMin_le α β x a)
  | inr b =>
      exact add_nonneg (x.2.1 _) (mul_nonneg (div_nonneg (by positivity) (by positivity))
        (affineBistellarLeftMin_nonneg α β x))

omit [Nonempty α] in
/-- The new-to-old coordinate formula is nonnegative. -/
theorem affineBistellarNewToOldFn_nonneg (x : stdSimplex ℝ (α ⊕ β)) (i : α ⊕ β) :
    0 ≤ affineBistellarNewToOldFn α β x i := by
  cases i with
  | inl a =>
      exact add_nonneg (x.2.1 _) (mul_nonneg (div_nonneg (by positivity) (by positivity))
        (affineBistellarRightMin_nonneg α β x))
  | inr b =>
      exact sub_nonneg.mpr (affineBistellarRightMin_le α β x b)

/-- The old-to-new coordinate formula preserves total barycentric mass. -/
theorem sum_affineBistellarOldToNewFn (x : stdSimplex ℝ (α ⊕ β)) :
    ∑ i, affineBistellarOldToNewFn α β x i = 1 := by
  rw [← Finset.univ_disjSum_univ, Finset.sum_disjSum]
  simp only [affineBistellarOldToNewFn, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hx : (∑ a, x (Sum.inl a)) + ∑ b, x (Sum.inr b) = 1 := by
    have hx := x.2.2
    rw [← Finset.univ_disjSum_univ, Finset.sum_disjSum] at hx
    exact hx
  rw [← hx]
  field_simp [card_cast_ne_zero α, card_cast_ne_zero β]
  ring

/-- The new-to-old coordinate formula preserves total barycentric mass. -/
theorem sum_affineBistellarNewToOldFn (x : stdSimplex ℝ (α ⊕ β)) :
    ∑ i, affineBistellarNewToOldFn α β x i = 1 := by
  rw [← Finset.univ_disjSum_univ, Finset.sum_disjSum]
  simp only [affineBistellarNewToOldFn, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hx : (∑ a, x (Sum.inl a)) + ∑ b, x (Sum.inr b) = 1 := by
    have hx := x.2.2
    rw [← Finset.univ_disjSum_univ, Finset.sum_disjSum] at hx
    exact hx
  rw [← hx]
  field_simp [card_cast_ne_zero α, card_cast_ne_zero β]
  ring

/-- The old-to-new formula as a self-map of the ambient standard simplex. -/
def affineBistellarOldToNewSimplex (x : stdSimplex ℝ (α ⊕ β)) :
    stdSimplex ℝ (α ⊕ β) :=
  ⟨affineBistellarOldToNewFn α β x,
    affineBistellarOldToNewFn_nonneg α β x,
    sum_affineBistellarOldToNewFn α β x⟩

@[simp]
theorem affineBistellarOldToNewSimplex_inl
    (x : stdSimplex ℝ (α ⊕ β)) (a : α) :
    affineBistellarOldToNewSimplex α β x (Sum.inl a) =
      x (Sum.inl a) - affineBistellarLeftMin α β x := rfl

@[simp]
theorem affineBistellarOldToNewSimplex_inr
    (x : stdSimplex ℝ (α ⊕ β)) (b : β) :
    affineBistellarOldToNewSimplex α β x (Sum.inr b) =
      x (Sum.inr b) + (Fintype.card α : ℝ) / (Fintype.card β : ℝ) *
        affineBistellarLeftMin α β x := rfl

/-- The new-to-old formula as a self-map of the ambient standard simplex. -/
def affineBistellarNewToOldSimplex (x : stdSimplex ℝ (α ⊕ β)) :
    stdSimplex ℝ (α ⊕ β) :=
  ⟨affineBistellarNewToOldFn α β x,
    affineBistellarNewToOldFn_nonneg α β x,
    sum_affineBistellarNewToOldFn α β x⟩

@[simp]
theorem affineBistellarNewToOldSimplex_inl
    (x : stdSimplex ℝ (α ⊕ β)) (a : α) :
    affineBistellarNewToOldSimplex α β x (Sum.inl a) =
      x (Sum.inl a) + (Fintype.card β : ℝ) / (Fintype.card α : ℝ) *
        affineBistellarRightMin α β x := rfl

@[simp]
theorem affineBistellarNewToOldSimplex_inr
    (x : stdSimplex ℝ (α ⊕ β)) (b : β) :
    affineBistellarNewToOldSimplex α β x (Sum.inr b) =
      x (Sum.inr b) - affineBistellarRightMin α β x := rfl

/-- The old-to-new formula always has a vanishing left coordinate. -/
theorem affineBistellarOldToNewSimplex_mem_new (x : stdSimplex ℝ (α ⊕ β)) :
    ∃ a : α, affineBistellarOldToNewSimplex α β x (Sum.inl a) = 0 := by
  obtain ⟨a, ha, hmin⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset α)) Finset.univ_nonempty (fun a ↦ x (Sum.inl a))
  refine ⟨a, ?_⟩
  rw [affineBistellarOldToNewSimplex_inl]
  change affineBistellarLeftMin α β x = x (Sum.inl a) at hmin
  rw [← hmin, sub_self]

/-- The new-to-old formula always has a vanishing right coordinate. -/
theorem affineBistellarNewToOldSimplex_mem_old (x : stdSimplex ℝ (α ⊕ β)) :
    ∃ b : β, affineBistellarNewToOldSimplex α β x (Sum.inr b) = 0 := by
  obtain ⟨b, hb, hmin⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset β)) Finset.univ_nonempty (fun b ↦ x (Sum.inr b))
  refine ⟨b, ?_⟩
  rw [affineBistellarNewToOldSimplex_inr]
  change affineBistellarRightMin α β x = x (Sum.inr b) at hmin
  rw [← hmin, sub_self]

/-- The old affine bistellar ball maps into the new one. -/
def affineBistellarOldToNew (x : affineBistellarOld α β) :
    affineBistellarNew α β :=
  ⟨affineBistellarOldToNewSimplex α β x,
    affineBistellarOldToNewSimplex_mem_new α β x⟩

/-- The new affine bistellar ball maps into the old one. -/
def affineBistellarNewToOld (x : affineBistellarNew α β) :
    affineBistellarOld α β :=
  ⟨affineBistellarNewToOldSimplex α β x,
    affineBistellarNewToOldSimplex_mem_old α β x⟩

@[simp]
theorem affineBistellarOldToNew_inl (x : affineBistellarOld α β) (a : α) :
    (affineBistellarOldToNew α β x).1 (Sum.inl a) =
      x.1 (Sum.inl a) - affineBistellarLeftMin α β x.1 := rfl

@[simp]
theorem affineBistellarOldToNew_inr (x : affineBistellarOld α β) (b : β) :
    (affineBistellarOldToNew α β x).1 (Sum.inr b) =
      x.1 (Sum.inr b) + (Fintype.card α : ℝ) / (Fintype.card β : ℝ) *
        affineBistellarLeftMin α β x.1 := rfl

@[simp]
theorem affineBistellarNewToOld_inl (x : affineBistellarNew α β) (a : α) :
    (affineBistellarNewToOld α β x).1 (Sum.inl a) =
      x.1 (Sum.inl a) + (Fintype.card β : ℝ) / (Fintype.card α : ℝ) *
        affineBistellarRightMin α β x.1 := rfl

@[simp]
theorem affineBistellarNewToOld_inr (x : affineBistellarNew α β) (b : β) :
    (affineBistellarNewToOld α β x).1 (Sum.inr b) =
      x.1 (Sum.inr b) - affineBistellarRightMin α β x.1 := rfl

/-- On the old carrier, the least transformed right coordinate is exactly the redistributed
mass. -/
theorem affineBistellarRightMin_oldToNew (x : affineBistellarOld α β) :
    affineBistellarRightMin α β (affineBistellarOldToNew α β x) =
      (Fintype.card α : ℝ) / (Fintype.card β : ℝ) *
        affineBistellarLeftMin α β x := by
  apply le_antisymm
  · obtain ⟨b, hb⟩ := x.2
    refine (affineBistellarRightMin_le α β _ b).trans_eq ?_
    simp [hb]
  · apply Finset.le_inf'
    intro b hb
    simp only [affineBistellarOldToNew_inr]
    exact le_add_of_nonneg_left (x.1.2.1 _)

/-- On the new carrier, the least transformed left coordinate is exactly the redistributed
mass. -/
theorem affineBistellarLeftMin_newToOld (x : affineBistellarNew α β) :
    affineBistellarLeftMin α β (affineBistellarNewToOld α β x) =
      (Fintype.card β : ℝ) / (Fintype.card α : ℝ) *
        affineBistellarRightMin α β x := by
  apply le_antisymm
  · obtain ⟨a, ha⟩ := x.2
    refine (affineBistellarLeftMin_le α β _ a).trans_eq ?_
    simp [ha]
  · apply Finset.le_inf'
    intro a ha
    simp only [affineBistellarNewToOld_inl]
    exact le_add_of_nonneg_left (x.1.2.1 _)

/-- The new-to-old formula is a left inverse of the old-to-new formula. -/
theorem affineBistellarNewToOld_oldToNew (x : affineBistellarOld α β) :
    affineBistellarNewToOld α β (affineBistellarOldToNew α β x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  cases i with
  | inl a =>
      change (x.1 (Sum.inl a) - affineBistellarLeftMin α β x.1) +
          (Fintype.card β : ℝ) / (Fintype.card α : ℝ) *
            affineBistellarRightMin α β (affineBistellarOldToNew α β x) =
        x.1 (Sum.inl a)
      rw [affineBistellarRightMin_oldToNew]
      field_simp [card_cast_ne_zero α, card_cast_ne_zero β]
      ring
  | inr b =>
      change (x.1 (Sum.inr b) + (Fintype.card α : ℝ) /
          (Fintype.card β : ℝ) * affineBistellarLeftMin α β x.1) -
          affineBistellarRightMin α β (affineBistellarOldToNew α β x) =
        x.1 (Sum.inr b)
      rw [affineBistellarRightMin_oldToNew]
      field_simp [card_cast_ne_zero α, card_cast_ne_zero β]
      ring

/-- The old-to-new formula is a left inverse of the new-to-old formula. -/
theorem affineBistellarOldToNew_newToOld (x : affineBistellarNew α β) :
    affineBistellarOldToNew α β (affineBistellarNewToOld α β x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  cases i with
  | inl a =>
      change (x.1 (Sum.inl a) + (Fintype.card β : ℝ) /
          (Fintype.card α : ℝ) * affineBistellarRightMin α β x.1) -
          affineBistellarLeftMin α β (affineBistellarNewToOld α β x) =
        x.1 (Sum.inl a)
      rw [affineBistellarLeftMin_newToOld]
      field_simp [card_cast_ne_zero α, card_cast_ne_zero β]
      ring
  | inr b =>
      change (x.1 (Sum.inr b) - affineBistellarRightMin α β x.1) +
          (Fintype.card α : ℝ) / (Fintype.card β : ℝ) *
            affineBistellarLeftMin α β (affineBistellarNewToOld α β x) =
        x.1 (Sum.inr b)
      rw [affineBistellarLeftMin_newToOld]
      field_simp [card_cast_ne_zero α, card_cast_ne_zero β]
      ring

/-- The old-to-new affine formula is continuous. -/
theorem continuous_affineBistellarOldToNew :
    Continuous (affineBistellarOldToNew α β) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have hval : Continuous (fun x : affineBistellarOld α β ↦
      (x.1.1 : α ⊕ β → ℝ)) :=
    (continuous_subtype_val : Continuous fun x : stdSimplex ℝ (α ⊕ β) ↦ x.1).comp
      (continuous_subtype_val : Continuous fun x : affineBistellarOld α β ↦ x.1)
  have hmin : Continuous (fun x : affineBistellarOld α β ↦
      affineBistellarLeftMin α β x.1) :=
    (continuous_affineBistellarLeftMin α β).comp continuous_subtype_val
  cases i with
  | inl a =>
      exact ((continuous_apply _).comp hval).sub hmin
  | inr b =>
      exact ((continuous_apply _).comp hval).add
        (continuous_const.mul hmin)

/-- The new-to-old affine formula is continuous. -/
theorem continuous_affineBistellarNewToOld :
    Continuous (affineBistellarNewToOld α β) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have hval : Continuous (fun x : affineBistellarNew α β ↦
      (x.1.1 : α ⊕ β → ℝ)) :=
    (continuous_subtype_val : Continuous fun x : stdSimplex ℝ (α ⊕ β) ↦ x.1).comp
      (continuous_subtype_val : Continuous fun x : affineBistellarNew α β ↦ x.1)
  have hmin : Continuous (fun x : affineBistellarNew α β ↦
      affineBistellarRightMin α β x.1) :=
    (continuous_affineBistellarRightMin α β).comp continuous_subtype_val
  cases i with
  | inl a =>
      exact ((continuous_apply _).comp hval).add
        (continuous_const.mul hmin)
  | inr b =>
      exact ((continuous_apply _).comp hval).sub hmin

/-- The two affine bistellar balls are homeomorphic by an explicit mass-redistribution map. -/
def affineBistellarHomeomorph :
    affineBistellarOld α β ≃ₜ affineBistellarNew α β where
  toFun := affineBistellarOldToNew α β
  invFun := affineBistellarNewToOld α β
  left_inv := affineBistellarNewToOld_oldToNew α β
  right_inv := affineBistellarOldToNew_newToOld α β
  continuous_toFun := continuous_affineBistellarOldToNew α β
  continuous_invFun := continuous_affineBistellarNewToOld α β

/-- The affine bistellar homeomorphism fixes every point of the common boundary. -/
theorem affineBistellarHomeomorph_fixed_of_left_zero
    (x : affineBistellarOld α β) (a : α) (ha : x.1 (Sum.inl a) = 0) :
    (affineBistellarHomeomorph α β x).1 = x.1 := by
  have hmin : affineBistellarLeftMin α β x.1 = 0 := by
    apply le_antisymm
    · exact (affineBistellarLeftMin_le α β x.1 a).trans_eq ha
    · exact affineBistellarLeftMin_nonneg α β x.1
  apply Subtype.ext
  funext i
  cases i with
  | inl a =>
      change x.1 (Sum.inl a) - affineBistellarLeftMin α β x.1 =
        x.1 (Sum.inl a)
      rw [hmin, sub_zero]
  | inr b =>
      change x.1 (Sum.inr b) + (Fintype.card α : ℝ) / (Fintype.card β : ℝ) *
          affineBistellarLeftMin α β x.1 = x.1 (Sum.inr b)
      rw [hmin, mul_zero, add_zero]

end Submission.FiniteOrderedComplex
