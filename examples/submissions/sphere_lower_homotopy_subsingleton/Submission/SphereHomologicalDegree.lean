/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.Homotopy
import Submission.Homology.SphereOne
import Mathlib.Algebra.Group.Int.Units

/-!
# The homological degree of a self-map of a sphere

This file packages the action of a self-map of `Sⁿ` on its top integral homology as an
integer.  It supplies the elementary functorial laws needed by the degree-classification
argument: homotopy invariance, normalization at the identity, and multiplicativity under
composition.

The sphere dimension is written `n + 1`, matching `Submission.hgrpSphereSelfIsoZ`.
-/

open CategoryTheory

noncomputable section

namespace Submission

/-- The endomorphism of `ℤ` induced by a self-map of `Sⁿ` on top integral homology. -/
def sphereHomologyEnd (n : ℕ)
    (f : TopCat.of (Sph (n + 1)) ⟶ TopCat.of (Sph (n + 1))) :
    AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
  (hgrpSphereSelfIsoZ n).inv ≫ HgrpMap (n + 1) f ≫
    (hgrpSphereSelfIsoZ n).hom

/-- The homological degree of a self-map of the positive-dimensional sphere `Sⁿ`. -/
def sphereHomologicalDegree (n : ℕ)
    (f : TopCat.of (Sph (n + 1)) ⟶ TopCat.of (Sph (n + 1))) : ℤ :=
  sphereHomologyEnd n f 1

/-- The action on top homology is multiplication by the homological degree. -/
theorem sphereHomologyEnd_apply (n : ℕ)
    (f : TopCat.of (Sph (n + 1)) ⟶ TopCat.of (Sph (n + 1))) (z : ℤ) :
    sphereHomologyEnd n f z = z * sphereHomologicalDegree n f := by
  rw [show z = z • (1 : ℤ) by simp]
  rw [map_zsmul]
  simp [sphereHomologicalDegree]

/-- Homotopic self-maps of a sphere have equal homological degree. -/
theorem sphereHomologicalDegree_homotopyInvariant (n : ℕ)
    {f g : TopCat.of (Sph (n + 1)) ⟶ TopCat.of (Sph (n + 1))}
    (H : TopCat.Homotopy f g) :
    sphereHomologicalDegree n f = sphereHomologicalDegree n g := by
  unfold sphereHomologicalDegree sphereHomologyEnd
  rw [HgrpMap_congr H]

/-- The same homotopy-invariance statement, packaged using Mathlib's `Homotopic` relation. -/
theorem sphereHomologicalDegree_homotopic (n : ℕ)
    {f g : TopCat.of (Sph (n + 1)) ⟶ TopCat.of (Sph (n + 1))}
    (H : ContinuousMap.Homotopic f.hom g.hom) :
    sphereHomologicalDegree n f = sphereHomologicalDegree n g := by
  obtain ⟨H⟩ := H
  exact sphereHomologicalDegree_homotopyInvariant n H

/-- The identity self-map of a sphere has homological degree one. -/
@[simp]
theorem sphereHomologicalDegree_id (n : ℕ) :
    sphereHomologicalDegree n (𝟙 (TopCat.of (Sph (n + 1)))) = 1 := by
  unfold sphereHomologicalDegree sphereHomologyEnd
  rw [HgrpMap_id]
  simp

/-- Conjugating the homology map by `Hₙ(Sⁿ) ≅ ℤ` respects composition. -/
theorem sphereHomologyEnd_comp (n : ℕ)
    (f g : TopCat.of (Sph (n + 1)) ⟶ TopCat.of (Sph (n + 1))) :
    sphereHomologyEnd n (f ≫ g) = sphereHomologyEnd n f ≫ sphereHomologyEnd n g := by
  unfold sphereHomologyEnd
  rw [HgrpMap_comp]
  simp

/-- Homological degree is multiplicative under composition. -/
theorem sphereHomologicalDegree_comp (n : ℕ)
    (f g : TopCat.of (Sph (n + 1)) ⟶ TopCat.of (Sph (n + 1))) :
    sphereHomologicalDegree n (f ≫ g) =
      sphereHomologicalDegree n f * sphereHomologicalDegree n g := by
  unfold sphereHomologicalDegree
  rw [sphereHomologyEnd_comp]
  rw [ConcreteCategory.comp_apply]
  exact sphereHomologyEnd_apply n g (sphereHomologyEnd n f 1)

/-- The constant self-map of a sphere with value `x`, factored through a point. -/
def sphereConst (n : ℕ) (x : Sph (n + 1)) :
    TopCat.of (Sph (n + 1)) ⟶ TopCat.of (Sph (n + 1)) :=
  toPt (TopCat.of (Sph (n + 1))) ≫ ptIncl x

/-- A constant sphere self-map acts by zero on positive-dimensional top homology. -/
@[simp]
theorem sphereHomologyEnd_const (n : ℕ) (x : Sph (n + 1)) :
    sphereHomologyEnd n (sphereConst n x) = 0 := by
  have hzero : HgrpMap (n + 1) (toPt (TopCat.of (Sph (n + 1)))) = 0 :=
    (isZero_Hgrp_punit (n + 1) n.succ_ne_zero).eq_zero_of_tgt _
  unfold sphereHomologyEnd sphereConst
  rw [HgrpMap_comp, hzero]
  simp

/-- A constant self-map of a positive-dimensional sphere has degree zero. -/
@[simp]
theorem sphereHomologicalDegree_const (n : ℕ) (x : Sph (n + 1)) :
    sphereHomologicalDegree n (sphereConst n x) = 0 := by
  unfold sphereHomologicalDegree
  rw [sphereHomologyEnd_const]
  rfl

/-- A right homotopy inverse forces the two homological degrees to multiply to one. -/
theorem sphereHomologicalDegree_mul_eq_one_of_homotopy (n : ℕ)
    (f g : TopCat.of (Sph (n + 1)) ⟶ TopCat.of (Sph (n + 1)))
    (H : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of (Sph (n + 1))))) :
    sphereHomologicalDegree n f * sphereHomologicalDegree n g = 1 := by
  rw [← sphereHomologicalDegree_comp]
  rw [sphereHomologicalDegree_homotopyInvariant n H]
  exact sphereHomologicalDegree_id n

/-- Every self-homotopy equivalence of a positive-dimensional sphere has degree `1` or `-1`. -/
theorem sphereHomologicalDegree_eq_one_or_neg_one_of_homotopyInverse (n : ℕ)
    (f g : TopCat.of (Sph (n + 1)) ⟶ TopCat.of (Sph (n + 1)))
    (H : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of (Sph (n + 1))))) :
    sphereHomologicalDegree n f = 1 ∨ sphereHomologicalDegree n f = -1 :=
  Int.eq_one_or_neg_one_of_mul_eq_one
    (sphereHomologicalDegree_mul_eq_one_of_homotopy n f g H)

end Submission
