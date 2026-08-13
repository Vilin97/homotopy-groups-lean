/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.HopfLocalTrivialization
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Short transport for the exact Hopf map

This file constructs a canonical lift of a pair consisting of a point of `S^3` and a
non-antipodal target point of `S^2`.  In complex notation, the construction applies the
rank-one projector determined by the target point and then normalizes.  It fixes the source
when the target is its Hopf image, varies continuously, and lies over the target.

The construction is the short-step input for a dyadic proof of the homotopy lifting property.
-/

open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

/-! ## The rank-one projector -/

/-- Euclidean scalar product on the exact `2`-sphere, written in coordinates. -/
def hopfBaseDot (y z : Sph 2) : ℝ :=
  (y : EuclideanSpace ℝ (Fin 3)) 0 * (z : EuclideanSpace ℝ (Fin 3)) 0 +
    (y : EuclideanSpace ℝ (Fin 3)) 1 * (z : EuclideanSpace ℝ (Fin 3)) 1 +
    (y : EuclideanSpace ℝ (Fin 3)) 2 * (z : EuclideanSpace ℝ (Fin 3)) 2

/-- The same scalar product with an arbitrary ambient vector in the second argument. -/
def hopfBaseDotVec (y : Sph 2) (z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (y : EuclideanSpace ℝ (Fin 3)) 0 * z 0 +
    (y : EuclideanSpace ℝ (Fin 3)) 1 * z 1 +
    (y : EuclideanSpace ℝ (Fin 3)) 2 * z 2

@[simp]
theorem hopfBaseDotVec_coe (y z : Sph 2) :
    hopfBaseDotVec y (z : EuclideanSpace ℝ (Fin 3)) = hopfBaseDot y z :=
  rfl

theorem continuous_hopfBaseDot :
    Continuous fun p : Sph 2 × Sph 2 => hopfBaseDot p.1 p.2 := by
  unfold hopfBaseDot
  fun_prop

/-- Apply the rank-one Hermitian projector associated to `y : S^2` to a vector in `R^4`.
The coordinate signs agree with `hopfVec`. -/
noncomputable def hopfProjectVec (y : Sph 2) (x : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![
    ((1 + (y : EuclideanSpace ℝ (Fin 3)) 0) * x 0 +
      (y : EuclideanSpace ℝ (Fin 3)) 1 * x 2 -
      (y : EuclideanSpace ℝ (Fin 3)) 2 * x 3) / 2,
    ((1 + (y : EuclideanSpace ℝ (Fin 3)) 0) * x 1 +
      (y : EuclideanSpace ℝ (Fin 3)) 1 * x 3 +
      (y : EuclideanSpace ℝ (Fin 3)) 2 * x 2) / 2,
    ((y : EuclideanSpace ℝ (Fin 3)) 1 * x 0 +
      (y : EuclideanSpace ℝ (Fin 3)) 2 * x 1 +
      (1 - (y : EuclideanSpace ℝ (Fin 3)) 0) * x 2) / 2,
    ((y : EuclideanSpace ℝ (Fin 3)) 1 * x 1 -
      (y : EuclideanSpace ℝ (Fin 3)) 2 * x 0 +
      (1 - (y : EuclideanSpace ℝ (Fin 3)) 0) * x 3) / 2]

@[simp] theorem hopfProjectVec_zero (y : Sph 2) (x : EuclideanSpace ℝ (Fin 4)) :
    hopfProjectVec y x 0 =
      ((1 + (y : EuclideanSpace ℝ (Fin 3)) 0) * x 0 +
        (y : EuclideanSpace ℝ (Fin 3)) 1 * x 2 -
        (y : EuclideanSpace ℝ (Fin 3)) 2 * x 3) / 2 := by
  simp [hopfProjectVec]

@[simp] theorem hopfProjectVec_one (y : Sph 2) (x : EuclideanSpace ℝ (Fin 4)) :
    hopfProjectVec y x 1 =
      ((1 + (y : EuclideanSpace ℝ (Fin 3)) 0) * x 1 +
        (y : EuclideanSpace ℝ (Fin 3)) 1 * x 3 +
        (y : EuclideanSpace ℝ (Fin 3)) 2 * x 2) / 2 := by
  simp [hopfProjectVec]

@[simp] theorem hopfProjectVec_two (y : Sph 2) (x : EuclideanSpace ℝ (Fin 4)) :
    hopfProjectVec y x 2 =
      ((y : EuclideanSpace ℝ (Fin 3)) 1 * x 0 +
        (y : EuclideanSpace ℝ (Fin 3)) 2 * x 1 +
        (1 - (y : EuclideanSpace ℝ (Fin 3)) 0) * x 2) / 2 := by
  simp [hopfProjectVec]

@[simp] theorem hopfProjectVec_three (y : Sph 2) (x : EuclideanSpace ℝ (Fin 4)) :
    hopfProjectVec y x 3 =
      ((y : EuclideanSpace ℝ (Fin 3)) 1 * x 1 -
        (y : EuclideanSpace ℝ (Fin 3)) 2 * x 0 +
        (1 - (y : EuclideanSpace ℝ (Fin 3)) 0) * x 3) / 2 := by
  simp [hopfProjectVec]

/-- The projector varies continuously in its sphere point and vector arguments. -/
theorem continuous_hopfProjectVec :
    Continuous fun p : Sph 2 × EuclideanSpace ℝ (Fin 4) => hopfProjectVec p.1 p.2 := by
  unfold hopfProjectVec
  fun_prop

/-- Squared norm of the projected vector, expressed as the projector expectation value. -/
theorem norm_hopfProjectVec_sq (y : Sph 2) (x : EuclideanSpace ℝ (Fin 4)) :
    ‖hopfProjectVec y x‖ ^ 2 =
      (‖x‖ ^ 2 + hopfBaseDotVec y (hopfVec x)) / 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [hopfProjectVec, hopfBaseDotVec, hopfVec, Fin.sum_univ_succ]
  have hs := sphereTwo_sum_sq y
  ring_nf at hs ⊢
  nlinarith

/-- For a unit source vector, the projector norm is controlled by the angle between its Hopf
image and the target. -/
theorem norm_hopfProjectVec_sq_of_sphere (y : Sph 2) (x : Sph 3) :
    ‖hopfProjectVec y (x : EuclideanSpace ℝ (Fin 4))‖ ^ 2 =
      (1 + hopfBaseDot y (hopfMap x)) / 2 := by
  rw [norm_hopfProjectVec_sq, norm_coe_sph]
  norm_num
  rfl

/-- Projecting a unit source vector along its own Hopf image fixes it. -/
theorem hopfProjectVec_hopfMap (x : Sph 3) :
    hopfProjectVec (hopfMap x) (x : EuclideanSpace ℝ (Fin 4)) =
      (x : EuclideanSpace ℝ (Fin 4)) := by
  have hs := sphereThree_sum_sq x
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [hopfMap, hopfVec]
    linear_combination
      (((x : EuclideanSpace ℝ (Fin 4)) 0) / 2) * hs
  · simp [hopfMap, hopfVec]
    linear_combination
      (((x : EuclideanSpace ℝ (Fin 4)) 1) / 2) * hs
  · simp [hopfMap, hopfVec]
    linear_combination
      (((x : EuclideanSpace ℝ (Fin 4)) 2) / 2) * hs
  · simp [hopfMap, hopfVec]
    linear_combination
      (((x : EuclideanSpace ℝ (Fin 4)) 3) / 2) * hs

/-- The Hopf vector of a projected vector points in the prescribed target direction. -/
theorem hopfVec_hopfProjectVec (y : Sph 2) (x : EuclideanSpace ℝ (Fin 4)) :
    hopfVec (hopfProjectVec y x) =
      ((‖x‖ ^ 2 + hopfBaseDotVec y (hopfVec x)) / 2) •
        (y : EuclideanSpace ℝ (Fin 3)) := by
  have hs := sphereTwo_sum_sq y
  rw [EuclideanSpace.real_norm_sq_eq]
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [hopfVec, hopfProjectVec, hopfBaseDotVec, Fin.sum_univ_succ]
    linear_combination
      (-(((x : EuclideanSpace ℝ (Fin 4)) 0) ^ 2 +
          ((x : EuclideanSpace ℝ (Fin 4)) 1) ^ 2 -
          ((x : EuclideanSpace ℝ (Fin 4)) 2) ^ 2 -
          ((x : EuclideanSpace ℝ (Fin 4)) 3) ^ 2) / 4) * hs
  · simp [hopfVec, hopfProjectVec, hopfBaseDotVec, Fin.sum_univ_succ]
    linear_combination
      (-(((x : EuclideanSpace ℝ (Fin 4)) 0) *
          ((x : EuclideanSpace ℝ (Fin 4)) 2) +
          ((x : EuclideanSpace ℝ (Fin 4)) 1) *
          ((x : EuclideanSpace ℝ (Fin 4)) 3)) / 2) * hs
  · simp [hopfVec, hopfProjectVec, hopfBaseDotVec, Fin.sum_univ_succ]
    linear_combination
      ((((x : EuclideanSpace ℝ (Fin 4)) 0) *
          ((x : EuclideanSpace ℝ (Fin 4)) 3) -
          ((x : EuclideanSpace ℝ (Fin 4)) 1) *
          ((x : EuclideanSpace ℝ (Fin 4)) 2)) / 2) * hs

/-- The Hopf quadratic formula is homogeneous of degree two. -/
theorem hopfVec_smul (r : ℝ) (x : EuclideanSpace ℝ (Fin 4)) :
    hopfVec (r • x) = r ^ 2 • hopfVec x := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [hopfVec] <;> ring

/-- Rephrase the projector-direction identity using the squared norm of the projection. -/
theorem hopfVec_hopfProjectVec_eq_norm_sq_smul
    (y : Sph 2) (x : EuclideanSpace ℝ (Fin 4)) :
    hopfVec (hopfProjectVec y x) =
      ‖hopfProjectVec y x‖ ^ 2 • (y : EuclideanSpace ℝ (Fin 3)) := by
  rw [hopfVec_hopfProjectVec, norm_hopfProjectVec_sq]

/-! ## The non-antipodal transport domain -/

/-- Pairs `(x,y)` for which the target `y` is not antipodal to `hopfMap x`. -/
abbrev HopfTransportDomain : Type :=
  {p : Sph 3 × Sph 2 // -1 < hopfBaseDot p.2 (hopfMap p.1)}

/-- The source point of a non-antipodal transport pair. -/
def HopfTransportDomain.source (p : HopfTransportDomain) : Sph 3 := p.1.1

/-- The target point of a non-antipodal transport pair. -/
def HopfTransportDomain.target (p : HopfTransportDomain) : Sph 2 := p.1.2

/-- The projected vector is nonzero throughout the non-antipodal domain. -/
theorem hopfProjectVec_ne_zero (p : HopfTransportDomain) :
    hopfProjectVec p.target (p.source : EuclideanSpace ℝ (Fin 4)) ≠ 0 := by
  intro hzero
  have hnorm := norm_hopfProjectVec_sq_of_sphere p.target p.source
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm
  have hp : -1 < hopfBaseDot p.target (hopfMap p.source) := p.property
  nlinarith

/-- The normalized ambient vector defining short Hopf transport. -/
noncomputable def hopfTransportVec (p : HopfTransportDomain) :
    EuclideanSpace ℝ (Fin 4) :=
  NormedSpace.normalize
    (hopfProjectVec p.target (p.source : EuclideanSpace ℝ (Fin 4)))

theorem norm_hopfTransportVec (p : HopfTransportDomain) : ‖hopfTransportVec p‖ = 1 := by
  exact NormedSpace.norm_normalize (hopfProjectVec_ne_zero p)

/-- Canonical transport in `S^3` toward a non-antipodal point of the base sphere. -/
noncomputable def hopfTransport (p : HopfTransportDomain) : Sph 3 :=
  ⟨hopfTransportVec p, mem_sphere_zero_iff_norm.mpr (norm_hopfTransportVec p)⟩

/-- The normalized ambient transport varies continuously on the non-antipodal domain. -/
theorem continuous_hopfTransportVec : Continuous hopfTransportVec := by
  have hargs : Continuous fun p : HopfTransportDomain =>
      (p.target, (p.source : EuclideanSpace ℝ (Fin 4))) := by
    unfold HopfTransportDomain.source HopfTransportDomain.target
    fun_prop
  have hv : Continuous fun p : HopfTransportDomain =>
      hopfProjectVec p.target (p.source : EuclideanSpace ℝ (Fin 4)) := by
    exact continuous_hopfProjectVec.comp hargs
  unfold hopfTransportVec NormedSpace.normalize
  exact (hv.norm.inv₀ fun p => norm_ne_zero_iff.mpr (hopfProjectVec_ne_zero p)).smul hv

/-- Short Hopf transport is continuous. -/
theorem continuous_hopfTransport : Continuous hopfTransport := by
  exact Continuous.subtype_mk continuous_hopfTransportVec fun p => by
    apply mem_sphere_zero_iff_norm.mpr
    exact norm_hopfTransportVec p

/-- The normalized projected vector has the prescribed Hopf direction. -/
theorem hopfVec_hopfTransportVec (p : HopfTransportDomain) :
    hopfVec (hopfTransportVec p) =
      (p.target : EuclideanSpace ℝ (Fin 3)) := by
  let v : EuclideanSpace ℝ (Fin 4) :=
    hopfProjectVec p.target (p.source : EuclideanSpace ℝ (Fin 4))
  have hv0 : v ≠ 0 := hopfProjectVec_ne_zero p
  have hnorm0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  change hopfVec (‖v‖⁻¹ • v) = (p.target : EuclideanSpace ℝ (Fin 3))
  rw [hopfVec_smul]
  have hdir : hopfVec v = ‖v‖ ^ 2 •
      (p.target : EuclideanSpace ℝ (Fin 3)) :=
    hopfVec_hopfProjectVec_eq_norm_sq_smul p.target
      (p.source : EuclideanSpace ℝ (Fin 4))
  rw [hdir, smul_smul]
  have hscalar : ‖v‖⁻¹ ^ 2 * ‖v‖ ^ 2 = 1 := by
    field_simp
  rw [hscalar, one_smul]

/-- Short Hopf transport lies over its target. -/
@[simp]
theorem hopfMap_hopfTransport (p : HopfTransportDomain) :
    hopfMap (hopfTransport p) = p.target := by
  apply Subtype.ext
  exact hopfVec_hopfTransportVec p

/-- A unit base vector has scalar product one with itself. -/
@[simp]
theorem hopfBaseDot_self (y : Sph 2) : hopfBaseDot y y = 1 := by
  simpa [hopfBaseDot, pow_two] using sphereTwo_sum_sq y

/-- The coordinate scalar product is symmetric. -/
theorem hopfBaseDot_comm (y z : Sph 2) : hopfBaseDot y z = hopfBaseDot z y := by
  unfold hopfBaseDot
  ring

/-- Chordal distance on the exact sphere in terms of the scalar product. -/
theorem dist_sq_eq_two_sub_two_mul_hopfBaseDot (y z : Sph 2) :
    dist y z ^ 2 = 2 - 2 * hopfBaseDot y z := by
  change ‖(y : EuclideanSpace ℝ (Fin 3)) -
      (z : EuclideanSpace ℝ (Fin 3))‖ ^ 2 = 2 - 2 * hopfBaseDot y z
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [hopfBaseDot, Fin.sum_univ_succ]
  have hy := sphereTwo_sum_sq y
  have hz := sphereTwo_sum_sq z
  ring_nf at hy hz ⊢
  nlinarith

/-- Points at chordal distance less than two are not antipodal. -/
theorem neg_one_lt_hopfBaseDot_of_dist_lt_two (y z : Sph 2)
    (h : dist y z < 2) : -1 < hopfBaseDot y z := by
  have hd : 0 ≤ dist y z := dist_nonneg
  have hsq : dist y z ^ 2 < 4 := by nlinarith
  rw [dist_sq_eq_two_sub_two_mul_hopfBaseDot] at hsq
  linarith

/-- Package a source and a target less than two units from its current Hopf image into the
transport domain. -/
noncomputable def hopfTransportDomainOfDistLtTwo (x : Sph 3) (y : Sph 2)
    (h : dist y (hopfMap x) < 2) : HopfTransportDomain :=
  ⟨(x, y), neg_one_lt_hopfBaseDot_of_dist_lt_two y (hopfMap x) h⟩

/-- The canonical point of the transport domain targeting the current Hopf image. -/
noncomputable def hopfTransportSelf (x : Sph 3) : HopfTransportDomain :=
  ⟨(x, hopfMap x), by simp⟩

/-- Transporting to the current Hopf image fixes the source. -/
@[simp]
theorem hopfTransport_self (x : Sph 3) :
    hopfTransport (hopfTransportSelf x) = x := by
  apply Subtype.ext
  change NormedSpace.normalize
      (hopfProjectVec (hopfMap x) (x : EuclideanSpace ℝ (Fin 4))) =
    (x : EuclideanSpace ℝ (Fin 4))
  rw [hopfProjectVec_hopfMap]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_coe_sph x)

end Submission
