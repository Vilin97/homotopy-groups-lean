/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectiveLine
import Submission.Topology.CellAttachment

/-!
# The projective-plane cell and the exact Hopf attaching map

This file constructs the characteristic map from the four-disk to the quotient-topology model of
complex projective two-space. Its restriction to the boundary factors through the projective line,
so it induces a map from the corresponding one-cell attachment to complex projective two-space.

After identifying the disk boundary with the exact metric three-sphere and the complex projective
line with the exact metric two-sphere, the attaching map is exactly the concrete quadratic Hopf map.
-/

open CategoryTheory Topology
open scoped Topology TopCat

noncomputable section

namespace Submission

noncomputable def complexProjectivePlaneDiskComplexPart
    (z : TopCat.disk.{0} 4) : ComplexEuclidean 1 :=
  (complexEuclideanRealLinearIsometryEquiv 1).symm z.down.val

theorem norm_complexProjectivePlaneDiskComplexPart_le
    (z : TopCat.disk.{0} 4) :
    ‖complexProjectivePlaneDiskComplexPart z‖ ≤ 1 := by
  rw [complexProjectivePlaneDiskComplexPart,
    (complexEuclideanRealLinearIsometryEquiv 1).symm.norm_map]
  have hz := z.down.property
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  exact hz

theorem continuous_complexProjectivePlaneDiskComplexPart :
    Continuous complexProjectivePlaneDiskComplexPart := by
  exact (complexEuclideanRealLinearIsometryEquiv 1).symm.continuous.comp
    (continuous_subtype_val.comp continuous_uliftDown)

noncomputable def complexProjectivePlaneDiskVec
    (z : TopCat.disk.{0} 4) : ComplexEuclidean 2 :=
  let w := complexProjectivePlaneDiskComplexPart z
  WithLp.toLp 2 ![w 0, w 1, (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ)]

theorem norm_complexProjectivePlaneDiskVec
    (z : TopCat.disk.{0} 4) : ‖complexProjectivePlaneDiskVec z‖ = 1 := by
  let w := complexProjectivePlaneDiskComplexPart z
  have hwle : ‖w‖ ≤ 1 := norm_complexProjectivePlaneDiskComplexPart_le z
  have harg : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  apply norm_eq_one_of_norm_sq_eq_one
  rw [EuclideanSpace.norm_sq_eq]
  simp [complexProjectivePlaneDiskVec, w, Fin.sum_univ_succ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt harg]
  have hw := EuclideanSpace.norm_sq_eq w
  simp [Fin.sum_univ_succ] at hw
  nlinarith

theorem continuous_complexProjectivePlaneDiskVec :
    Continuous complexProjectivePlaneDiskVec := by
  unfold complexProjectivePlaneDiskVec
  have hw : Continuous complexProjectivePlaneDiskComplexPart :=
    continuous_complexProjectivePlaneDiskComplexPart
  fun_prop

noncomputable def complexProjectivePlaneDiskLift :
    C(TopCat.disk.{0} 4, ComplexUnitSphere 2) where
  toFun z := ⟨complexProjectivePlaneDiskVec z, by
    rw [Metric.mem_sphere, dist_zero_right, norm_complexProjectivePlaneDiskVec]⟩
  continuous_toFun := Continuous.subtype_mk
    continuous_complexProjectivePlaneDiskVec (fun z ↦ by
      rw [Metric.mem_sphere, dist_zero_right, norm_complexProjectivePlaneDiskVec])

noncomputable def complexProjectivePlaneCharacteristic :
    TopCat.disk.{0} 4 ⟶ TopCat.of (ComplexProjectiveModel 2) :=
  TopCat.ofHom ((complexHopfMap 2).comp complexProjectivePlaneDiskLift)

noncomputable def diskBoundaryFourToComplexUnitSphere
    (z : TopCat.diskBoundary.{0} 4) : ComplexUnitSphere 1 :=
  ⟨(complexEuclideanRealLinearIsometryEquiv 1).symm z.down.val, by
    rw [Metric.mem_sphere, dist_zero_right,
      (complexEuclideanRealLinearIsometryEquiv 1).symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp z.down.property⟩

theorem continuous_diskBoundaryFourToComplexUnitSphere :
    Continuous diskBoundaryFourToComplexUnitSphere := by
  apply Continuous.subtype_mk
  exact (complexEuclideanRealLinearIsometryEquiv 1).symm.continuous.comp
    (continuous_subtype_val.comp continuous_uliftDown)

noncomputable def diskBoundaryFourComplexHopfMap :
    TopCat.diskBoundary.{0} 4 ⟶ TopCat.of (ComplexProjectiveModel 1) :=
  TopCat.ofHom ((complexHopfMap 1).comp
    ⟨diskBoundaryFourToComplexUnitSphere,
      continuous_diskBoundaryFourToComplexUnitSphere⟩)

noncomputable def complexProjectivePlaneBottomInclVec
    (w : ComplexEuclidean 1) : ComplexEuclidean 2 :=
  WithLp.toLp 2 ![w 0, w 1, 0]

theorem continuous_complexProjectivePlaneBottomInclVec :
    Continuous complexProjectivePlaneBottomInclVec := by
  unfold complexProjectivePlaneBottomInclVec
  fun_prop

theorem complexProjectivePlaneBottomInclVec_injective :
    Function.Injective complexProjectivePlaneBottomInclVec := by
  intro x y h
  apply PiLp.ext
  intro i
  fin_cases i
  · have h0 := congrArg (fun w : ComplexEuclidean 2 ↦ w 0) h
    simpa [complexProjectivePlaneBottomInclVec] using h0
  · have h1 := congrArg (fun w : ComplexEuclidean 2 ↦ w 1) h
    simpa [complexProjectivePlaneBottomInclVec] using h1

noncomputable def complexProjectivePlaneBottomInclLinear :
    ComplexEuclidean 1 →ₗ[ℂ] ComplexEuclidean 2 where
  toFun := complexProjectivePlaneBottomInclVec
  map_add' x y := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [complexProjectivePlaneBottomInclVec]
  map_smul' c x := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [complexProjectivePlaneBottomInclVec]

noncomputable def complexProjectivePlaneBottomIncl :
    ComplexProjectiveModel 1 → ComplexProjectiveModel 2 :=
  Projectivization.map complexProjectivePlaneBottomInclLinear
    complexProjectivePlaneBottomInclVec_injective

theorem complexProjectivePlaneBottomIncl_mk
    (w : ComplexEuclidean 1) (hw : w ≠ 0) :
    complexProjectivePlaneBottomIncl (Projectivization.mk ℂ w hw) =
      Projectivization.mk ℂ (complexProjectivePlaneBottomInclVec w)
        (by
          intro hzero
          apply hw
          apply complexProjectivePlaneBottomInclVec_injective
          simpa [complexProjectivePlaneBottomInclVec] using hzero) :=
  rfl

theorem continuous_complexProjectivePlaneBottomIncl :
    Continuous complexProjectivePlaneBottomIncl := by
  apply (complexHopfMap_isQuotientMap 1).continuous_iff.mpr
  change Continuous fun x : ComplexUnitSphere 1 ↦
    Projectivization.mk ℂ
      (complexProjectivePlaneBottomInclVec (x : ComplexEuclidean 1)) _
  apply continuous_quotient_mk'.comp
  exact Continuous.subtype_mk
    (continuous_complexProjectivePlaneBottomInclVec.comp continuous_subtype_val) _

noncomputable def complexProjectivePlaneBottomInclTopCat :
    TopCat.of (ComplexProjectiveModel 1) ⟶ TopCat.of (ComplexProjectiveModel 2) :=
  TopCat.ofHom ⟨complexProjectivePlaneBottomIncl,
    continuous_complexProjectivePlaneBottomIncl⟩

theorem complexProjectivePlaneCharacteristic_boundary :
    diskBoundaryFourComplexHopfMap ≫ complexProjectivePlaneBottomInclTopCat =
      TopCat.diskBoundaryIncl 4 ≫ complexProjectivePlaneCharacteristic := by
  apply TopCat.hom_ext
  ext z
  change complexProjectivePlaneBottomIncl
      (complexHopfMap 1 (diskBoundaryFourToComplexUnitSphere z)) =
    complexHopfMap 2 (complexProjectivePlaneDiskLift (TopCat.diskBoundaryIncl 4 z))
  change complexProjectivePlaneBottomIncl
      (Projectivization.mk ℂ
        (diskBoundaryFourToComplexUnitSphere z : ComplexEuclidean 1) _) =
    Projectivization.mk ℂ
      (complexProjectivePlaneDiskLift (TopCat.diskBoundaryIncl 4 z) :
        ComplexEuclidean 2) _
  have hpart :
      complexProjectivePlaneDiskComplexPart (TopCat.diskBoundaryIncl 4 z) =
        (diskBoundaryFourToComplexUnitSphere z : ComplexEuclidean 1) := by
    unfold complexProjectivePlaneDiskComplexPart diskBoundaryFourToComplexUnitSphere
    congr 2
  rw [complexProjectivePlaneBottomIncl_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨1, ?_⟩
  apply PiLp.ext
  intro i
  simp only [one_smul]
  fin_cases i
  · simp [complexProjectivePlaneDiskLift, complexProjectivePlaneDiskVec,
      hpart, complexProjectivePlaneBottomInclVec]
  · simp [complexProjectivePlaneDiskLift, complexProjectivePlaneDiskVec,
      hpart, complexProjectivePlaneBottomInclVec]
  · simp only [complexProjectivePlaneDiskLift, complexProjectivePlaneDiskVec,
      complexProjectivePlaneBottomInclVec]
    change (Real.sqrt
      (1 - ‖complexProjectivePlaneDiskComplexPart (TopCat.diskBoundaryIncl 4 z)‖ ^ 2) : ℂ) = 0
    have hn : ‖complexProjectivePlaneDiskComplexPart (TopCat.diskBoundaryIncl 4 z)‖ = 1 := by
      rw [complexProjectivePlaneDiskComplexPart,
        (complexEuclideanRealLinearIsometryEquiv 1).symm.norm_map]
      exact mem_sphere_zero_iff_norm.mp z.down.property
    rw [hn]
    norm_num

/-- The one-cell attachment determined by the complex Hopf quotient. -/
noncomputable abbrev complexProjectivePlaneCell : TopCat.{0} :=
  cellAttachment diskBoundaryFourComplexHopfMap

/-- The canonical map from the projective two-cell attachment to complex projective space. -/
noncomputable def complexProjectivePlaneCellMap :
    complexProjectivePlaneCell ⟶ TopCat.of (ComplexProjectiveModel 2) :=
  cellAttachmentDesc diskBoundaryFourComplexHopfMap
    complexProjectivePlaneBottomInclTopCat
    complexProjectivePlaneCharacteristic
    complexProjectivePlaneCharacteristic_boundary

@[simp]
theorem complexProjectivePlaneCellMap_incl :
    cellAttachmentIncl diskBoundaryFourComplexHopfMap ≫
        complexProjectivePlaneCellMap =
      complexProjectivePlaneBottomInclTopCat := by
  rw [complexProjectivePlaneCellMap, cellAttachmentIncl_desc]

@[simp]
theorem complexProjectivePlaneCellMap_disk :
    cellAttachmentDisk diskBoundaryFourComplexHopfMap ≫
        complexProjectivePlaneCellMap =
      complexProjectivePlaneCharacteristic := by
  rw [complexProjectivePlaneCellMap, cellAttachmentDisk_desc]

/-- The standard boundary of the four-disk is the exact metric three-sphere. -/
noncomputable def diskBoundaryFourHomeomorphSphereThree :
    TopCat.diskBoundary.{0} 4 ≃ₜ Sph 3 :=
  Homeomorph.ulift

theorem complexUnitSphereHomeomorphSphere_diskBoundaryFour
    (z : TopCat.diskBoundary.{0} 4) :
    complexUnitSphereHomeomorphSphere 1
        (diskBoundaryFourToComplexUnitSphere z) =
      diskBoundaryFourHomeomorphSphereThree z := by
  apply Subtype.ext
  exact (complexEuclideanRealLinearIsometryEquiv 1).apply_symm_apply z.down.val

/-- After the projective-line and realification identifications, the attaching map of the
projective two-cell is exactly the concrete quadratic Hopf map. -/
theorem diskBoundaryFourComplexHopfMap_is_hopfMap :
    diskBoundaryFourComplexHopfMap ≫
        TopCat.ofHom (complexProjectiveLineHomeomorphSphere :
          C(ComplexProjectiveModel 1, Sph 2)) =
      TopCat.ofHom (diskBoundaryFourHomeomorphSphereThree :
          C(TopCat.diskBoundary.{0} 4, Sph 3)) ≫ TopCat.ofHom hopfMap := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change complexProjectiveLineHomeomorphSphere
      (complexHopfMap 1 (diskBoundaryFourToComplexUnitSphere z)) =
    hopfMap (diskBoundaryFourHomeomorphSphereThree z)
  rw [complexProjectiveLineHomeomorphSphere_complexHopfMap,
    complexUnitSphereHomeomorphSphere_diskBoundaryFour]

end Submission
