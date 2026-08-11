/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ChallengeDeps
import Mathlib
import Submission.ForMathlib.HomotopyGroup.Basic

/-!
# The fundamental group of the metric circle

This file closes the model gap between Mathlib's complex unit circle and the exact metric
`SphereSpace 1` used by the benchmark.  The source circle computation uses the exponential
covering.  Homotopy invariance then transports it across an explicit homeomorphism which sends
the standard point `1 : Circle` to `sphereBasepoint 1`.
-/

open HomotopyGroups
open scoped Topology

noncomputable section

namespace Submission

private def intAddEquivZMultiplesTwoPi :
    ℤ ≃+ AddSubgroup.zmultiples (2 * Real.pi) := by
  let f : ℤ →+ AddSubgroup.zmultiples (2 * Real.pi) :=
    { toFun := fun n =>
        ⟨n • (2 * Real.pi), AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := by intro m n; ext; simp [add_mul] }
  exact AddEquiv.ofBijective f ⟨by
    intro m n h
    apply smul_left_injective ℤ Real.two_pi_pos.ne'
    exact congrArg Subtype.val h
  , by
    rintro ⟨r, hr⟩
    rcases AddSubgroup.mem_zmultiples_iff.mp hr with ⟨n, rfl⟩
    exact ⟨n, rfl⟩⟩

private theorem pi1CircleMulEquivInt :
    Nonempty
      (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃*
        Multiplicative ℤ) := by
  let e : Circle.exp ⁻¹' ({1} : Set Circle) := ⟨0, by simp⟩
  let coverEquiv := Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e
  exact ⟨HomotopyGroup.pi1MulEquivFundamentalGroup.trans <|
    coverEquiv.trans <| MulOpposite.opMulEquiv.symm.trans <|
      intAddEquivZMultiplesTwoPi.symm.toMultiplicative⟩

/-- The standard complex unit circle as the benchmark's metric `SphereSpace 1`. -/
def circleHomeomorphMetricSphereOne : Circle ≃ₜ SphereSpace 1 where
  toFun z := ⟨Complex.orthonormalBasisOneI.repr z, by
    rw [Metric.mem_sphere, dist_zero_right]
    rw [Complex.orthonormalBasisOneI.repr.norm_map]
    exact Circle.norm_coe z⟩
  invFun z := ⟨Complex.orthonormalBasisOneI.repr.symm z, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp z.property⟩
  left_inv z := Circle.ext (Complex.orthonormalBasisOneI.repr.symm_apply_apply z)
  right_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.apply_symm_apply z)
  continuous_toFun :=
    (Complex.orthonormalBasisOneI.repr.continuous.comp continuous_subtype_val).subtype_mk
      (fun z => by
        rw [Metric.mem_sphere, dist_zero_right]
        change ‖Complex.orthonormalBasisOneI.repr (z : ℂ)‖ = 1
        rw [Complex.orthonormalBasisOneI.repr.norm_map]
        exact Circle.norm_coe z)
  continuous_invFun :=
    (Complex.orthonormalBasisOneI.repr.symm.continuous.comp continuous_subtype_val).subtype_mk
      (fun z => by
        apply mem_sphere_zero_iff_norm.mpr
        change ‖Complex.orthonormalBasisOneI.repr.symm
          (z : EuclideanSpace ℝ (Fin 2))‖ = 1
        rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
        exact mem_sphere_zero_iff_norm.mp z.property)

@[simp]
theorem circleHomeomorphMetricSphereOne_one :
    circleHomeomorphMetricSphereOne (1 : Circle) = sphereBasepoint 1 := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [circleHomeomorphMetricSphereOne, sphereBasepoint]

/-- The fundamental group of the benchmark's exact metric circle is infinite cyclic. -/
theorem pi1_sphere_one_mulEquiv_int :
    Nonempty
      (HomotopyGroup.Pi 1 (SphereSpace 1) (sphereBasepoint 1) ≃*
        Multiplicative ℤ) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_homotopyEquiv'
    (N := Fin 1) circleHomeomorphMetricSphereOne.toHomotopyEquiv (1 : Circle)
  change HomotopyGroup.Pi 1 Circle (1 : Circle) ≃*
    HomotopyGroup.Pi 1 (SphereSpace 1) (circleHomeomorphMetricSphereOne 1) at e
  rw [circleHomeomorphMetricSphereOne_one] at e
  obtain ⟨c⟩ := pi1CircleMulEquivInt
  exact ⟨e.symm.trans c⟩

end Submission
