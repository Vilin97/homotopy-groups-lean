/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homotopy.TopologicalGroup
import Submission.Model.Sphere
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.Analysis.Quaternion
import Mathlib.Topology.Algebra.Module.TransferInstance

/-!
# The exact three-sphere as the unit-quaternion topological group

The maintained exact model of `S³` is the unit sphere in four-dimensional Euclidean space.
Quaternion coordinates give an isometric homeomorphism from this sphere to the unit quaternions.
We transport the group structure back across that homeomorphism and record its identity and
inverse in the maintained coordinates.
-/

open Metric
open scoped Quaternion Topology Topology.Homotopy

noncomputable section

namespace Submission

/-- The unit quaternions, carrying their inherited topological-group structure. -/
abbrev UnitQuaternion := Metric.sphere (0 : Quaternion ℝ) 1

/-- The exact metric three-sphere is homeomorphic to the unit quaternions by the standard
ordered coordinates `(re, imI, imJ, imK)`. -/
noncomputable def sphereThreeUnitQuaternionHomeomorph : Sph 3 ≃ₜ UnitQuaternion where
  toFun x := ⟨Quaternion.linearIsometryEquivTuple.symm x, by
    rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
    exact mem_sphere_zero_iff_norm.mp x.2⟩
  invFun q := ⟨Quaternion.linearIsometryEquivTuple q, by
    rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
    exact mem_sphere_zero_iff_norm.mp q.2⟩
  left_inv x := by
    apply Subtype.ext
    exact Quaternion.linearIsometryEquivTuple.apply_symm_apply x
  right_inv q := by
    apply Subtype.ext
    exact Quaternion.linearIsometryEquivTuple.symm_apply_apply q
  continuous_toFun := Continuous.subtype_mk
    (Quaternion.linearIsometryEquivTuple.symm.continuous.comp continuous_subtype_val)
    (fun x ↦ by
      rw [mem_sphere_zero_iff_norm]
      change ‖Quaternion.linearIsometryEquivTuple.symm
        (x : EuclideanSpace ℝ (Fin 4))‖ = 1
      rw [LinearIsometryEquiv.norm_map]
      exact mem_sphere_zero_iff_norm.mp x.2)
  continuous_invFun := Continuous.subtype_mk
    (Quaternion.linearIsometryEquivTuple.continuous.comp continuous_subtype_val)
    (fun q ↦ by
      rw [mem_sphere_zero_iff_norm]
      change ‖Quaternion.linearIsometryEquivTuple (q : Quaternion ℝ)‖ = 1
      rw [LinearIsometryEquiv.norm_map]
      exact mem_sphere_zero_iff_norm.mp q.2)

/-- The exact three-sphere inherits its group law from unit-quaternion multiplication. -/
noncomputable instance sphereThreeGroup : Group (Sph 3) :=
  sphereThreeUnitQuaternionHomeomorph.toEquiv.group

/-- Quaternion coordinates form a continuous multiplicative equivalence. -/
noncomputable def sphereThreeUnitQuaternionContinuousMulEquiv :
    Sph 3 ≃ₜ* UnitQuaternion :=
  ContinuousMulEquiv.mk' sphereThreeUnitQuaternionHomeomorph (fun _ _ ↦ by
    change sphereThreeUnitQuaternionHomeomorph
        (sphereThreeUnitQuaternionHomeomorph.symm
          (sphereThreeUnitQuaternionHomeomorph _ * sphereThreeUnitQuaternionHomeomorph _)) = _
    rw [Homeomorph.apply_symm_apply])

/-- The transported unit-quaternion law makes the exact three-sphere a topological group. -/
noncomputable instance sphereThreeIsTopologicalGroup : IsTopologicalGroup (Sph 3) :=
  sphereThreeUnitQuaternionContinuousMulEquiv.isTopologicalGroup

/-- The maintained sphere basepoint is the quaternionic unit. -/
@[simp]
theorem sphereThreeUnitQuaternionHomeomorph_basepoint :
    sphereThreeUnitQuaternionHomeomorph (sphereBasepoint 3) = (1 : UnitQuaternion) := by
  apply Subtype.ext
  change Quaternion.linearIsometryEquivTuple.symm
      (EuclideanSpace.single 0 1) = (1 : Quaternion ℝ)
  change
    ({ re := (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 4)) 0
       imI := (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 4)) 1
       imJ := (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 4)) 2
       imK := (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 4)) 3 } :
      Quaternion ℝ) = 1
  apply Quaternion.ext <;> simp

/-- The group identity agrees with the maintained first-coordinate sphere basepoint. -/
@[simp]
theorem sphereThree_one_eq_basepoint : (1 : Sph 3) = sphereBasepoint 3 := by
  apply sphereThreeUnitQuaternionContinuousMulEquiv.injective
  rw [map_one]
  exact sphereThreeUnitQuaternionHomeomorph_basepoint.symm

/-- A unit quaternion is inverted by quaternionic conjugation. -/
theorem unitQuaternion_coe_inv (q : UnitQuaternion) :
    ((q⁻¹ : UnitQuaternion) : Quaternion ℝ) = star (q : Quaternion ℝ) := by
  rw [Metric.unitSphere.coe_inv, Quaternion.inv_def]
  have hnorm : ‖(q : Quaternion ℝ)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp q.2
  rw [Quaternion.normSq_eq_norm_mul_self, hnorm, one_mul, inv_one, one_smul]

/-- In maintained coordinates, unit-quaternion inversion fixes the real coordinate and negates
all three imaginary coordinates. -/
theorem sphereThree_inv_apply (x : Sph 3) (i : Fin 4) :
    ((x⁻¹ : Sph 3) : EuclideanSpace ℝ (Fin 4)) i =
      if i = 0 then (x : EuclideanSpace ℝ (Fin 4)) i
        else -(x : EuclideanSpace ℝ (Fin 4)) i := by
  have hmap := sphereThreeUnitQuaternionContinuousMulEquiv.map_inv x
  change sphereThreeUnitQuaternionHomeomorph (x⁻¹) =
    (sphereThreeUnitQuaternionHomeomorph x)⁻¹ at hmap
  have hq := congrArg Subtype.val hmap
  change Quaternion.linearIsometryEquivTuple.symm
      ((x⁻¹ : Sph 3) : EuclideanSpace ℝ (Fin 4)) =
    (((sphereThreeUnitQuaternionHomeomorph x)⁻¹ : UnitQuaternion) : Quaternion ℝ) at hq
  rw [unitQuaternion_coe_inv] at hq
  change Quaternion.linearIsometryEquivTuple.symm
      ((x⁻¹ : Sph 3) : EuclideanSpace ℝ (Fin 4)) =
    star (Quaternion.linearIsometryEquivTuple.symm
      (x : EuclideanSpace ℝ (Fin 4))) at hq
  have hv := congrArg Quaternion.linearIsometryEquivTuple hq
  rw [Quaternion.linearIsometryEquivTuple.apply_symm_apply] at hv
  have hi := congrArg (fun v : EuclideanSpace ℝ (Fin 4) ↦ v i) hv
  rw [Quaternion.linearIsometryEquivTuple_symm_apply] at hi
  fin_cases i <;>
    simpa [Quaternion.linearIsometryEquivTuple] using hi

end Submission
