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

theorem complexProjectivePlaneBottomIncl_injective :
    Function.Injective complexProjectivePlaneBottomIncl :=
  Projectivization.map_injective complexProjectivePlaneBottomInclLinear
    complexProjectivePlaneBottomInclVec_injective

theorem complexProjectivePlaneDiskSqrt_eq_zero_iff
    (z : TopCat.disk.{0} 4) :
    Real.sqrt (1 - ‖complexProjectivePlaneDiskComplexPart z‖ ^ 2) = 0 ↔
      ‖complexProjectivePlaneDiskComplexPart z‖ = 1 := by
  let w := complexProjectivePlaneDiskComplexPart z
  have hwle : ‖w‖ ≤ 1 := norm_complexProjectivePlaneDiskComplexPart_le z
  have harg : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  constructor
  · intro hsqrt
    have hsquare := Real.sq_sqrt harg
    rw [hsqrt] at hsquare
    nlinarith [norm_nonneg w]
  · intro hnorm
    rw [hnorm]
    norm_num

noncomputable def complexProjectivePlaneDiskBoundaryOfNormEqOne
    (z : TopCat.disk.{0} 4)
    (hz : ‖complexProjectivePlaneDiskComplexPart z‖ = 1) :
    TopCat.diskBoundary.{0} 4 :=
  ULift.up ⟨z.down.val, by
    rw [mem_sphere_zero_iff_norm]
    calc
      ‖z.down.val‖ =
          ‖(complexEuclideanRealLinearIsometryEquiv 1).symm z.down.val‖ :=
        ((complexEuclideanRealLinearIsometryEquiv 1).symm.norm_map z.down.val).symm
      _ = 1 := by
        simpa [complexProjectivePlaneDiskComplexPart] using hz⟩

@[simp]
theorem diskBoundaryIncl_diskBoundaryOfNormEqOne
    (z : TopCat.disk.{0} 4)
    (hz : ‖complexProjectivePlaneDiskComplexPart z‖ = 1) :
    TopCat.diskBoundaryIncl 4
        (complexProjectivePlaneDiskBoundaryOfNormEqOne z hz) = z := by
  apply ULift.ext
  apply Subtype.ext
  rfl

theorem complexProjectivePlaneDisk_norm_eq_one_of_bottom_eq
    (p : ComplexProjectiveModel 1) (z : TopCat.disk.{0} 4)
    (h : complexProjectivePlaneBottomIncl p =
      complexProjectivePlaneCharacteristic z) :
    ‖complexProjectivePlaneDiskComplexPart z‖ = 1 := by
  obtain ⟨x, rfl⟩ := (complexHopfMap_isQuotientMap 1).surjective p
  change Projectivization.mk ℂ
      (complexProjectivePlaneBottomInclVec (x : ComplexEuclidean 1)) _ =
    Projectivization.mk ℂ (complexProjectivePlaneDiskVec z) _ at h
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨c, hc⟩ := h
  have hcne : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hc
    have hzero : (x : ComplexEuclidean 1) = 0 := by
      apply complexProjectivePlaneBottomInclVec_injective
      simpa [complexProjectivePlaneBottomInclVec] using hc.symm
    exact complexUnitSphere_ne_zero x hzero
  have hthird := congrArg (fun w : ComplexEuclidean 2 ↦ w 2) hc
  have hsqrt : Real.sqrt
      (1 - ‖complexProjectivePlaneDiskComplexPart z‖ ^ 2) = 0 := by
    simp only [complexProjectivePlaneDiskVec,
      complexProjectivePlaneBottomInclVec] at hthird
    simpa [hcne] using hthird
  exact (complexProjectivePlaneDiskSqrt_eq_zero_iff z).mp hsqrt

theorem complexProjectivePlaneCharacteristic_injective_of_sqrt_ne_zero
    (z w : TopCat.disk.{0} 4)
    (hz : Real.sqrt
      (1 - ‖complexProjectivePlaneDiskComplexPart z‖ ^ 2) ≠ 0)
    (h : complexProjectivePlaneCharacteristic z =
      complexProjectivePlaneCharacteristic w) :
    z = w := by
  change Projectivization.mk ℂ (complexProjectivePlaneDiskVec z) _ =
    Projectivization.mk ℂ (complexProjectivePlaneDiskVec w) _ at h
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨c, hc⟩ := h
  have hcnorm : ‖c‖ = 1 := by
    have hnorm := congrArg norm hc
    rw [norm_smul, norm_complexProjectivePlaneDiskVec,
      norm_complexProjectivePlaneDiskVec, mul_one] at hnorm
    exact hnorm
  have hthird := congrArg (fun v : ComplexEuclidean 2 ↦ v 2) hc
  simp only [complexProjectivePlaneDiskVec] at hthird
  let rz := Real.sqrt (1 - ‖complexProjectivePlaneDiskComplexPart z‖ ^ 2)
  let rw := Real.sqrt (1 - ‖complexProjectivePlaneDiskComplexPart w‖ ^ 2)
  have hrz : 0 ≤ rz := Real.sqrt_nonneg _
  have hrw : 0 ≤ rw := Real.sqrt_nonneg _
  have hrwne : rw ≠ 0 := by
    intro hrw0
    apply hz
    change rz = 0
    change c • (rw : ℂ) = (rz : ℂ) at hthird
    have hczero : (rz : ℂ) = 0 := by
      simpa [hrw0] using hthird.symm
    exact Complex.ofReal_eq_zero.mp hczero
  have hr : rw = rz := by
    have hnormthird := congrArg norm hthird
    change ‖c • (rw : ℂ)‖ = ‖(rz : ℂ)‖ at hnormthird
    rw [norm_smul, hcnorm, one_mul] at hnormthird
    simpa [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hrw, abs_of_nonneg hrz] using hnormthird
  have hc_one : c = 1 := by
    change c * (rw : ℂ) = (rz : ℂ) at hthird
    rw [← hr] at hthird
    exact (mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hrwne))
      (by simpa using hthird)
  rw [hc_one, one_smul] at hc
  have hpart : complexProjectivePlaneDiskComplexPart w =
      complexProjectivePlaneDiskComplexPart z := by
    apply PiLp.ext
    intro i
    fin_cases i
    · have hzero := congrArg (fun v : ComplexEuclidean 2 ↦ v 0) hc
      simpa [complexProjectivePlaneDiskVec] using hzero
    · have hone := congrArg (fun v : ComplexEuclidean 2 ↦ v 1) hc
      simpa [complexProjectivePlaneDiskVec] using hone
  apply ULift.ext
  apply Subtype.ext
  apply (complexEuclideanRealLinearIsometryEquiv 1).symm.injective
  simpa [complexProjectivePlaneDiskComplexPart] using hpart.symm

theorem complexProjectivePlaneCell_disk_eq_incl_of_norm_eq_one
    (z : TopCat.disk.{0} 4)
    (hz : ‖complexProjectivePlaneDiskComplexPart z‖ = 1) :
    cellAttachmentDisk diskBoundaryFourComplexHopfMap z =
      cellAttachmentIncl diskBoundaryFourComplexHopfMap
        (diskBoundaryFourComplexHopfMap
          (complexProjectivePlaneDiskBoundaryOfNormEqOne z hz)) := by
  let b := complexProjectivePlaneDiskBoundaryOfNormEqOne z hz
  calc
    cellAttachmentDisk diskBoundaryFourComplexHopfMap z =
        cellAttachmentDisk diskBoundaryFourComplexHopfMap
          (TopCat.diskBoundaryIncl 4 b) := by
      rw [diskBoundaryIncl_diskBoundaryOfNormEqOne]
    _ = cellAttachmentIncl diskBoundaryFourComplexHopfMap
          (diskBoundaryFourComplexHopfMap b) :=
      (ConcreteCategory.congr_hom
        (cellAttachment_condition diskBoundaryFourComplexHopfMap) b).symm

theorem complexProjectivePlaneCell_incl_eq_disk_of_image_eq
    (p : ComplexProjectiveModel 1) (z : TopCat.disk.{0} 4)
    (h : complexProjectivePlaneBottomIncl p =
      complexProjectivePlaneCharacteristic z) :
    cellAttachmentIncl diskBoundaryFourComplexHopfMap p =
      cellAttachmentDisk diskBoundaryFourComplexHopfMap z := by
  have hz := complexProjectivePlaneDisk_norm_eq_one_of_bottom_eq p z h
  let b := complexProjectivePlaneDiskBoundaryOfNormEqOne z hz
  have hbottom :
      complexProjectivePlaneBottomIncl (diskBoundaryFourComplexHopfMap b) =
        complexProjectivePlaneBottomIncl p := by
    calc
      complexProjectivePlaneBottomIncl (diskBoundaryFourComplexHopfMap b) =
          complexProjectivePlaneCharacteristic (TopCat.diskBoundaryIncl 4 b) :=
        ConcreteCategory.congr_hom
          complexProjectivePlaneCharacteristic_boundary b
      _ = complexProjectivePlaneCharacteristic z := by
        rw [diskBoundaryIncl_diskBoundaryOfNormEqOne]
      _ = complexProjectivePlaneBottomIncl p := h.symm
  have hp : diskBoundaryFourComplexHopfMap b = p :=
    complexProjectivePlaneBottomIncl_injective hbottom
  calc
    cellAttachmentIncl diskBoundaryFourComplexHopfMap p =
        cellAttachmentIncl diskBoundaryFourComplexHopfMap
          (diskBoundaryFourComplexHopfMap b) := by rw [hp]
    _ = cellAttachmentDisk diskBoundaryFourComplexHopfMap
          (TopCat.diskBoundaryIncl 4 b) :=
      ConcreteCategory.congr_hom
        (cellAttachment_condition diskBoundaryFourComplexHopfMap) b
    _ = cellAttachmentDisk diskBoundaryFourComplexHopfMap z := by
      rw [diskBoundaryIncl_diskBoundaryOfNormEqOne]

theorem complexProjectivePlaneCell_disk_eq_disk_of_image_eq
    (z w : TopCat.disk.{0} 4)
    (h : complexProjectivePlaneCharacteristic z =
      complexProjectivePlaneCharacteristic w) :
    cellAttachmentDisk diskBoundaryFourComplexHopfMap z =
      cellAttachmentDisk diskBoundaryFourComplexHopfMap w := by
  by_cases hz : Real.sqrt
      (1 - ‖complexProjectivePlaneDiskComplexPart z‖ ^ 2) = 0
  · have hznorm := (complexProjectivePlaneDiskSqrt_eq_zero_iff z).mp hz
    let b := complexProjectivePlaneDiskBoundaryOfNormEqOne z hznorm
    calc
      cellAttachmentDisk diskBoundaryFourComplexHopfMap z =
          cellAttachmentIncl diskBoundaryFourComplexHopfMap
            (diskBoundaryFourComplexHopfMap b) :=
        complexProjectivePlaneCell_disk_eq_incl_of_norm_eq_one z hznorm
      _ = cellAttachmentDisk diskBoundaryFourComplexHopfMap w :=
        complexProjectivePlaneCell_incl_eq_disk_of_image_eq _ _ <| by
          calc
            complexProjectivePlaneBottomIncl (diskBoundaryFourComplexHopfMap b) =
                complexProjectivePlaneCharacteristic
                  (TopCat.diskBoundaryIncl 4 b) :=
              ConcreteCategory.congr_hom
                complexProjectivePlaneCharacteristic_boundary b
            _ = complexProjectivePlaneCharacteristic z := by
              rw [diskBoundaryIncl_diskBoundaryOfNormEqOne]
            _ = complexProjectivePlaneCharacteristic w := h
  · rw [complexProjectivePlaneCharacteristic_injective_of_sqrt_ne_zero z w hz h]

theorem complexProjectivePlaneCellMap_injective :
    Function.Injective complexProjectivePlaneCellMap := by
  intro x y hxy
  obtain ⟨x, rfl⟩ :=
    (pushoutSumDesc_isQuotientMap diskBoundaryFourComplexHopfMap
      (TopCat.diskBoundaryIncl 4)).surjective x
  obtain ⟨y, rfl⟩ :=
    (pushoutSumDesc_isQuotientMap diskBoundaryFourComplexHopfMap
      (TopCat.diskBoundaryIncl 4)).surjective y
  rcases x with p | z <;> rcases y with q | w
  · have hp := ConcreteCategory.congr_hom
      complexProjectivePlaneCellMap_incl p
    have hq := ConcreteCategory.congr_hom
      complexProjectivePlaneCellMap_incl q
    have hxy' := hp.symm.trans (hxy.trans hq)
    change cellAttachmentIncl diskBoundaryFourComplexHopfMap p =
      cellAttachmentIncl diskBoundaryFourComplexHopfMap q
    rw [complexProjectivePlaneBottomIncl_injective hxy']
  · have hp := ConcreteCategory.congr_hom
      complexProjectivePlaneCellMap_incl p
    have hw := ConcreteCategory.congr_hom
      complexProjectivePlaneCellMap_disk w
    have hxy' := hp.symm.trans (hxy.trans hw)
    change cellAttachmentIncl diskBoundaryFourComplexHopfMap p =
      cellAttachmentDisk diskBoundaryFourComplexHopfMap w
    exact complexProjectivePlaneCell_incl_eq_disk_of_image_eq p w hxy'
  · have hz := ConcreteCategory.congr_hom
      complexProjectivePlaneCellMap_disk z
    have hq := ConcreteCategory.congr_hom
      complexProjectivePlaneCellMap_incl q
    have hxy' := hz.symm.trans (hxy.trans hq)
    change cellAttachmentDisk diskBoundaryFourComplexHopfMap z =
      cellAttachmentIncl diskBoundaryFourComplexHopfMap q
    exact (complexProjectivePlaneCell_incl_eq_disk_of_image_eq q z hxy'.symm).symm
  · have hz := ConcreteCategory.congr_hom
      complexProjectivePlaneCellMap_disk z
    have hw := ConcreteCategory.congr_hom
      complexProjectivePlaneCellMap_disk w
    have hxy' := hz.symm.trans (hxy.trans hw)
    change cellAttachmentDisk diskBoundaryFourComplexHopfMap z =
      cellAttachmentDisk diskBoundaryFourComplexHopfMap w
    exact complexProjectivePlaneCell_disk_eq_disk_of_image_eq z w hxy'

noncomputable def complexPhaseToNonnegativeReal (c : ℂ) : Circle :=
  if hc : c = 0 then 1 else
    ⟨c⁻¹ * (‖c‖ : ℂ), mem_sphere_zero_iff_norm.mpr <| by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg c),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc)]⟩

theorem complexPhaseToNonnegativeReal_mul (c : ℂ) :
    (complexPhaseToNonnegativeReal c : ℂ) * c = (‖c‖ : ℂ) := by
  by_cases hc : c = 0
  · simp [complexPhaseToNonnegativeReal, hc]
  · rw [complexPhaseToNonnegativeReal, dif_neg hc]
    change (c⁻¹ * (‖c‖ : ℂ)) * c = (‖c‖ : ℂ)
    rw [mul_right_comm, inv_mul_cancel₀ hc, one_mul]

noncomputable def complexProjectivePlanePhaseNormalized
    (x : ComplexUnitSphere 2) : ComplexUnitSphere 2 :=
  complexUnitSphereCircleAction 2
    (complexPhaseToNonnegativeReal ((x : ComplexEuclidean 2) 2)) x

theorem complexProjectivePlanePhaseNormalized_two
    (x : ComplexUnitSphere 2) :
    (complexProjectivePlanePhaseNormalized x : ComplexEuclidean 2) 2 =
      (‖(x : ComplexEuclidean 2) 2‖ : ℂ) := by
  change (complexPhaseToNonnegativeReal ((x : ComplexEuclidean 2) 2) : ℂ) *
      (x : ComplexEuclidean 2) 2 = _
  exact complexPhaseToNonnegativeReal_mul _

noncomputable def complexProjectivePlanePhaseNormalizedPart
    (x : ComplexUnitSphere 2) : ComplexEuclidean 1 :=
  let y := complexProjectivePlanePhaseNormalized x
  WithLp.toLp 2 ![(y : ComplexEuclidean 2) 0, (y : ComplexEuclidean 2) 1]

theorem norm_complexProjectivePlanePhaseNormalizedPart_le
    (x : ComplexUnitSphere 2) :
    ‖complexProjectivePlanePhaseNormalizedPart x‖ ≤ 1 := by
  let y := complexProjectivePlanePhaseNormalized x
  let w := complexProjectivePlanePhaseNormalizedPart x
  have hy := EuclideanSpace.norm_sq_eq (y : ComplexEuclidean 2)
  have hw := EuclideanSpace.norm_sq_eq w
  simp [Fin.sum_univ_succ] at hy
  simp [Fin.sum_univ_succ] at hw
  change ‖w‖ ^ 2 = ‖(y : ComplexEuclidean 2) 0‖ ^ 2 +
    ‖(y : ComplexEuclidean 2) 1‖ ^ 2 at hw
  change ‖w‖ ≤ 1
  nlinarith [norm_nonneg w, sq_nonneg ‖(y : ComplexEuclidean 2) 2‖]

noncomputable def complexProjectivePlaneDiskOfUnitSphere
    (x : ComplexUnitSphere 2) : TopCat.disk.{0} 4 :=
  ULift.up ⟨complexEuclideanRealLinearIsometryEquiv 1
      (complexProjectivePlanePhaseNormalizedPart x), by
    rw [Metric.mem_closedBall, dist_zero_right,
      (complexEuclideanRealLinearIsometryEquiv 1).norm_map]
    exact norm_complexProjectivePlanePhaseNormalizedPart_le x⟩

@[simp]
theorem complexProjectivePlaneDiskComplexPart_diskOfUnitSphere
    (x : ComplexUnitSphere 2) :
    complexProjectivePlaneDiskComplexPart
        (complexProjectivePlaneDiskOfUnitSphere x) =
      complexProjectivePlanePhaseNormalizedPart x := by
  exact (complexEuclideanRealLinearIsometryEquiv 1).symm_apply_apply _

theorem complexProjectivePlaneDiskOfUnitSphere_sqrt
    (x : ComplexUnitSphere 2) :
    Real.sqrt
        (1 - ‖complexProjectivePlaneDiskComplexPart
          (complexProjectivePlaneDiskOfUnitSphere x)‖ ^ 2) =
      ‖(x : ComplexEuclidean 2) 2‖ := by
  let y := complexProjectivePlanePhaseNormalized x
  let w := complexProjectivePlanePhaseNormalizedPart x
  have hy := EuclideanSpace.norm_sq_eq (y : ComplexEuclidean 2)
  have hw := EuclideanSpace.norm_sq_eq w
  simp [Fin.sum_univ_succ] at hy hw
  change ‖w‖ ^ 2 = ‖(y : ComplexEuclidean 2) 0‖ ^ 2 +
    ‖(y : ComplexEuclidean 2) 1‖ ^ 2 at hw
  have hy2 : ‖(y : ComplexEuclidean 2) 2‖ =
      ‖(x : ComplexEuclidean 2) 2‖ := by
    rw [complexProjectivePlanePhaseNormalized_two]
    simp
  rw [hy2] at hy
  rw [complexProjectivePlaneDiskComplexPart_diskOfUnitSphere]
  change Real.sqrt (1 - ‖w‖ ^ 2) = ‖(x : ComplexEuclidean 2) 2‖
  rw [show 1 - ‖w‖ ^ 2 = ‖(x : ComplexEuclidean 2) 2‖ ^ 2 by
    nlinarith [sq_nonneg ‖(y : ComplexEuclidean 2) 2‖]]
  exact Real.sqrt_sq (norm_nonneg _)

theorem complexProjectivePlaneDiskVec_diskOfUnitSphere
    (x : ComplexUnitSphere 2) :
    complexProjectivePlaneDiskVec
        (complexProjectivePlaneDiskOfUnitSphere x) =
      (complexProjectivePlanePhaseNormalized x : ComplexEuclidean 2) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [complexProjectivePlaneDiskVec,
      complexProjectivePlanePhaseNormalizedPart]
  · simp [complexProjectivePlaneDiskVec,
      complexProjectivePlanePhaseNormalizedPart]
  · change (Real.sqrt
        (1 - ‖complexProjectivePlaneDiskComplexPart
          (complexProjectivePlaneDiskOfUnitSphere x)‖ ^ 2) : ℂ) =
      (complexProjectivePlanePhaseNormalized x : ComplexEuclidean 2) 2
    rw [complexProjectivePlaneDiskOfUnitSphere_sqrt,
      complexProjectivePlanePhaseNormalized_two]

theorem complexProjectivePlaneCharacteristic_diskOfUnitSphere
    (x : ComplexUnitSphere 2) :
    complexProjectivePlaneCharacteristic
        (complexProjectivePlaneDiskOfUnitSphere x) =
      complexHopfMap 2 x := by
  change complexHopfMap 2
      (complexProjectivePlaneDiskLift
        (complexProjectivePlaneDiskOfUnitSphere x)) =
    complexHopfMap 2 x
  have hlift : complexProjectivePlaneDiskLift
      (complexProjectivePlaneDiskOfUnitSphere x) =
        complexProjectivePlanePhaseNormalized x := by
    apply Subtype.ext
    exact complexProjectivePlaneDiskVec_diskOfUnitSphere x
  rw [hlift]
  exact complexHopfMap_circleAction 2
    (complexPhaseToNonnegativeReal ((x : ComplexEuclidean 2) 2)) x

theorem complexProjectivePlaneCharacteristic_surjective :
    Function.Surjective complexProjectivePlaneCharacteristic := by
  intro p
  obtain ⟨x, rfl⟩ := (complexHopfMap_isQuotientMap 2).surjective p
  exact ⟨complexProjectivePlaneDiskOfUnitSphere x,
    complexProjectivePlaneCharacteristic_diskOfUnitSphere x⟩

theorem complexProjectivePlaneCellMap_surjective :
    Function.Surjective complexProjectivePlaneCellMap := by
  intro p
  obtain ⟨z, rfl⟩ := complexProjectivePlaneCharacteristic_surjective p
  exact ⟨cellAttachmentDisk diskBoundaryFourComplexHopfMap z,
    ConcreteCategory.congr_hom complexProjectivePlaneCellMap_disk z⟩

/-- The canonical map from the Hopf cell attachment to complex projective two-space is
bijective. -/
theorem complexProjectivePlaneCellMap_bijective :
    Function.Bijective complexProjectivePlaneCellMap :=
  ⟨complexProjectivePlaneCellMap_injective,
    complexProjectivePlaneCellMap_surjective⟩

/-- Complex projective two-space is the result of attaching a four-cell to the projective line
along the exact complex Hopf quotient. -/
noncomputable def complexProjectivePlaneCellHomeomorph :
    complexProjectivePlaneCell ≃ₜ ComplexProjectiveModel 2 :=
  IsHomeomorph.homeomorph complexProjectivePlaneCellMap <|
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨complexProjectivePlaneCellMap.hom.continuous,
        complexProjectivePlaneCellMap_bijective⟩

@[simp]
theorem complexProjectivePlaneCellHomeomorph_incl
    (p : ComplexProjectiveModel 1) :
    complexProjectivePlaneCellHomeomorph
        (cellAttachmentIncl diskBoundaryFourComplexHopfMap p) =
      complexProjectivePlaneBottomIncl p :=
  ConcreteCategory.congr_hom complexProjectivePlaneCellMap_incl p

@[simp]
theorem complexProjectivePlaneCellHomeomorph_disk
    (z : TopCat.disk.{0} 4) :
    complexProjectivePlaneCellHomeomorph
        (cellAttachmentDisk diskBoundaryFourComplexHopfMap z) =
      complexProjectivePlaneCharacteristic z :=
  ConcreteCategory.congr_hom complexProjectivePlaneCellMap_disk z

end Submission
