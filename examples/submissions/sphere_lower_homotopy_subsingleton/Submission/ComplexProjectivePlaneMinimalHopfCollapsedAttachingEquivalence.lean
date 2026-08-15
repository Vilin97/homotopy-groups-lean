/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfCollapsedAttachingPushout

/-!
# Homotopy equivalence with the collapsed attaching pushout

The relative 120-step collapse is a strong deformation retraction: its retraction stays constant
throughout the deformation.  Using the cofibration of the remaining four-simplex boundary, the
homotopy extension property adjusts the four-simplex map so that it glues to the target inclusion.
The resulting map is an explicit homotopy inverse to the canonical comparison from the realized
nine-vertex projective plane to the collapsed attaching pushout.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial TopCat
open scoped unitInterval Topology Topology.Homotopy

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable local instance minimalHopfCollapsedAttachingBoundaryInclCofibration :
    IsCofibration
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex) :=
  minimalHopfProjectivePlaneInteriorBoundaryRealizationInclSimplex_isCofibration

noncomputable def minimalHopfCollapsedAttachingBoundaryHomotopy :
    ContinuousMap.Homotopy
      ((SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl).hom.comp
        (SSet.toTop.map
          minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured).hom)
      ((SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl).hom.comp
        (minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.toFun.comp
          (minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun.comp
            (SSet.toTop.map
              minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured).hom))) := by
  simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
    (ContinuousMap.Homotopy.refl
      (SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl).hom).comp
        (minimalHopfProjectivePlanePuncturedRealizationDeformation.symm.compContinuousMap
          (SSet.toTop.map
            minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured).hom)

noncomputable def minimalHopfCollapsedAttachingBoundaryHomotopyCurried :
    SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlaneInteriorBoundaryFacets) ⟶
      TopCat.of C(I, projectivePlaneRealization) :=
  TopCat.ofHom minimalHopfCollapsedAttachingBoundaryHomotopy.toContinuousMap.argSwap.curry

theorem minimalHopfCollapsedAttachingBoundaryHomotopySq :
    CommSq minimalHopfCollapsedAttachingBoundaryHomotopyCurried
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex)
      (PathSpace.eval₀ projectivePlaneRealization)
      (SSet.toTop.map minimalHopfProjectivePlaneInteriorSimplexSSetIncl) := by
  constructor
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change minimalHopfCollapsedAttachingBoundaryHomotopy (0, x) =
    SSet.toTop.map minimalHopfProjectivePlaneInteriorSimplexSSetIncl
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex x)
  rw [ContinuousMap.Homotopy.apply_zero]
  exact ConcreteCategory.congr_hom
    minimalHopfProjectivePlanePuncturedSimplexRealization_isPushout.w x

noncomputable def minimalHopfCollapsedAttachingSimplexPathExtension :
    SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlaneInteriorSimplexFacets) ⟶
      TopCat.of C(I, projectivePlaneRealization) :=
  ((inferInstance : HasLiftingProperty
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex)
      (PathSpace.eval₀ projectivePlaneRealization)).sq_hasLift
        minimalHopfCollapsedAttachingBoundaryHomotopySq).exists_lift.some.l

theorem minimalHopfCollapsedAttachingSimplexPathExtension_boundary :
    SSet.toTop.map
          minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex ≫
        minimalHopfCollapsedAttachingSimplexPathExtension =
      minimalHopfCollapsedAttachingBoundaryHomotopyCurried :=
  ((inferInstance : HasLiftingProperty
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex)
      (PathSpace.eval₀ projectivePlaneRealization)).sq_hasLift
        minimalHopfCollapsedAttachingBoundaryHomotopySq).exists_lift.some.fac_left

theorem minimalHopfCollapsedAttachingSimplexPathExtension_zero :
    minimalHopfCollapsedAttachingSimplexPathExtension ≫ PathSpace.eval₀ projectivePlaneRealization =
      SSet.toTop.map minimalHopfProjectivePlaneInteriorSimplexSSetIncl :=
  ((inferInstance : HasLiftingProperty
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex)
      (PathSpace.eval₀ projectivePlaneRealization)).sq_hasLift
        minimalHopfCollapsedAttachingBoundaryHomotopySq).exists_lift.some.fac_right

noncomputable def minimalHopfCollapsedAttachingAdjustedSimplexMap :
    SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlaneInteriorSimplexFacets) ⟶
      projectivePlaneRealization :=
  minimalHopfCollapsedAttachingSimplexPathExtension ≫ PathSpace.evalAt projectivePlaneRealization 1

noncomputable def minimalHopfCollapsedAttachingTargetToProjectivePlane :
    SSet.toTop.obj (orderedSSet minimalHopfTargetFacets) ⟶
      projectivePlaneRealization :=
  TopCat.ofHom minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.toFun ≫
    SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl

theorem minimalHopfCollapsedAttachingInverse_boundary :
    minimalHopfProjectivePlaneTargetAttachingMap ≫
        minimalHopfCollapsedAttachingTargetToProjectivePlane =
      SSet.toTop.map
          minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex ≫
        minimalHopfCollapsedAttachingAdjustedSimplexMap := by
  rw [minimalHopfCollapsedAttachingAdjustedSimplexMap, ← Category.assoc,
    minimalHopfCollapsedAttachingSimplexPathExtension_boundary]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change _ = minimalHopfCollapsedAttachingBoundaryHomotopy (1, x)
  rw [ContinuousMap.Homotopy.apply_one]
  rfl

noncomputable def minimalHopfCollapsedAttachingPushoutToProjectivePlane :
    minimalHopfCollapsedAttachingPushout ⟶ projectivePlaneRealization :=
  minimalHopfCollapsedAttachingPushout_isPushout.desc
    minimalHopfCollapsedAttachingTargetToProjectivePlane minimalHopfCollapsedAttachingAdjustedSimplexMap minimalHopfCollapsedAttachingInverse_boundary

@[reassoc]
theorem minimalHopfCollapsedAttachingInverse_target :
    minimalHopfCollapsedAttachingPushoutTargetIncl ≫ minimalHopfCollapsedAttachingPushoutToProjectivePlane =
      minimalHopfCollapsedAttachingTargetToProjectivePlane := by
  apply minimalHopfCollapsedAttachingPushout_isPushout.inl_desc

@[reassoc]
theorem minimalHopfCollapsedAttachingInverse_simplex :
    minimalHopfCollapsedAttachingPushoutSimplexIncl ≫ minimalHopfCollapsedAttachingPushoutToProjectivePlane =
      minimalHopfCollapsedAttachingAdjustedSimplexMap := by
  apply minimalHopfCollapsedAttachingPushout_isPushout.inr_desc

noncomputable def minimalHopfCollapsedAttachingPuncturedHomotopyForward :
    ContinuousMap.Homotopy
      (SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl).hom
      ((SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl).hom.comp
        (minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.toFun.comp
          minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun)) := by
  simpa only [ContinuousMap.comp_id] using
    (ContinuousMap.Homotopy.refl
      (SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl).hom).comp
        minimalHopfProjectivePlanePuncturedRealizationDeformation.symm

noncomputable def minimalHopfCollapsedAttachingSimplexToProjectivePlaneHomotopyForward :
    ContinuousMap.Homotopy
      (SSet.toTop.map minimalHopfProjectivePlaneInteriorSimplexSSetIncl).hom
      minimalHopfCollapsedAttachingAdjustedSimplexMap.hom where
  toFun p := minimalHopfCollapsedAttachingSimplexPathExtension p.2 p.1
  continuous_toFun := minimalHopfCollapsedAttachingSimplexPathExtension.hom.uncurry.continuous.comp
    (continuous_snd.prodMk continuous_fst)
  map_zero_left x := by
    exact ConcreteCategory.congr_hom minimalHopfCollapsedAttachingSimplexPathExtension_zero x
  map_one_left _ := rfl

noncomputable def minimalHopfCollapsedAttachingPuncturedHomotopyForwardCurried :
    SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlanePuncturedFacets) ⟶
      TopCat.of C(I, projectivePlaneRealization) :=
  TopCat.ofHom minimalHopfCollapsedAttachingPuncturedHomotopyForward.toContinuousMap.argSwap.curry

noncomputable def minimalHopfCollapsedAttachingSimplexToProjectivePlaneHomotopyForwardCurried :
    SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlaneInteriorSimplexFacets) ⟶
      TopCat.of C(I, projectivePlaneRealization) :=
  TopCat.ofHom
    minimalHopfCollapsedAttachingSimplexToProjectivePlaneHomotopyForward.toContinuousMap.argSwap.curry

theorem minimalHopfCollapsedAttachingForwardHomotopies_boundary :
    SSet.toTop.map
          minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured ≫
        minimalHopfCollapsedAttachingPuncturedHomotopyForwardCurried =
      SSet.toTop.map
          minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex ≫
        minimalHopfCollapsedAttachingSimplexToProjectivePlaneHomotopyForwardCurried := by
  rw [minimalHopfCollapsedAttachingSimplexToProjectivePlaneHomotopyForwardCurried]
  change _ = SSet.toTop.map
      minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex ≫
        minimalHopfCollapsedAttachingSimplexPathExtension
  rw [minimalHopfCollapsedAttachingSimplexPathExtension_boundary]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro t
  rfl

noncomputable def minimalHopfCollapsedAttachingProjectivePlanePath :
    projectivePlaneRealization ⟶ TopCat.of C(I, projectivePlaneRealization) :=
  minimalHopfProjectivePlanePuncturedSimplexRealization_isPushout.desc
    minimalHopfCollapsedAttachingPuncturedHomotopyForwardCurried
    minimalHopfCollapsedAttachingSimplexToProjectivePlaneHomotopyForwardCurried
    minimalHopfCollapsedAttachingForwardHomotopies_boundary

@[reassoc]
theorem minimalHopfCollapsedAttachingProjectivePlanePath_punctured :
    SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl ≫
        minimalHopfCollapsedAttachingProjectivePlanePath =
      minimalHopfCollapsedAttachingPuncturedHomotopyForwardCurried := by
  apply minimalHopfProjectivePlanePuncturedSimplexRealization_isPushout.inl_desc

@[reassoc]
theorem minimalHopfCollapsedAttachingProjectivePlanePath_simplex :
    SSet.toTop.map minimalHopfProjectivePlaneInteriorSimplexSSetIncl ≫
      minimalHopfCollapsedAttachingProjectivePlanePath =
      minimalHopfCollapsedAttachingSimplexToProjectivePlaneHomotopyForwardCurried := by
  apply minimalHopfProjectivePlanePuncturedSimplexRealization_isPushout.inr_desc

theorem minimalHopfCollapsedAttachingProjectivePlanePath_zero :
    minimalHopfCollapsedAttachingProjectivePlanePath ≫ PathSpace.eval₀ projectivePlaneRealization =
      𝟙 projectivePlaneRealization := by
  apply minimalHopfProjectivePlanePuncturedSimplexRealization_isPushout.hom_ext
  · rw [← Category.assoc, minimalHopfCollapsedAttachingProjectivePlanePath_punctured]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact minimalHopfCollapsedAttachingPuncturedHomotopyForward.apply_zero x
  · rw [← Category.assoc, minimalHopfCollapsedAttachingProjectivePlanePath_simplex]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact minimalHopfCollapsedAttachingSimplexToProjectivePlaneHomotopyForward.apply_zero x

theorem minimalHopfCollapsedAttachingProjectivePlanePath_one :
    minimalHopfCollapsedAttachingProjectivePlanePath ≫ PathSpace.evalAt projectivePlaneRealization 1 =
      minimalHopfProjectivePlaneToCollapsedAttachingPushout ≫ minimalHopfCollapsedAttachingPushoutToProjectivePlane := by
  apply minimalHopfProjectivePlanePuncturedSimplexRealization_isPushout.hom_ext
  · rw [← Category.assoc, minimalHopfCollapsedAttachingProjectivePlanePath_punctured]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change minimalHopfCollapsedAttachingPuncturedHomotopyForward (1, x) =
      minimalHopfCollapsedAttachingPushoutToProjectivePlane
        (minimalHopfProjectivePlaneToCollapsedAttachingPushout
          (SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl x))
    rw [ContinuousMap.Homotopy.apply_one]
    have hp := ConcreteCategory.congr_hom
      minimalHopfProjectivePlanePuncturedIncl_toCollapsedAttachingPushout x
    rw [ConcreteCategory.comp_apply] at hp
    rw [hp]
    simp only [ConcreteCategory.comp_apply, ContinuousMap.comp_apply]
    change SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl
        (minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.toFun
          (minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun x)) =
      minimalHopfCollapsedAttachingPushoutToProjectivePlane
        (minimalHopfCollapsedAttachingPushoutTargetIncl
          (minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun x))
    have hi := ConcreteCategory.congr_hom minimalHopfCollapsedAttachingInverse_target
      (minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun x)
    rw [ConcreteCategory.comp_apply] at hi
    rw [hi]
    rfl
  · rw [← Category.assoc, minimalHopfCollapsedAttachingProjectivePlanePath_simplex]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change minimalHopfCollapsedAttachingSimplexToProjectivePlaneHomotopyForward (1, x) =
      minimalHopfCollapsedAttachingPushoutToProjectivePlane
        (minimalHopfProjectivePlaneToCollapsedAttachingPushout
          (SSet.toTop.map minimalHopfProjectivePlaneInteriorSimplexSSetIncl x))
    rw [ContinuousMap.Homotopy.apply_one]
    have hp := ConcreteCategory.congr_hom
      minimalHopfProjectivePlaneInteriorSimplexIncl_toCollapsedAttachingPushout x
    rw [ConcreteCategory.comp_apply] at hp
    rw [hp]
    exact (ConcreteCategory.congr_hom minimalHopfCollapsedAttachingInverse_simplex x).symm

noncomputable def minimalHopfCollapsedAttachingProjectivePlaneHomotopyForward :
    ContinuousMap.Homotopy
      (ContinuousMap.id projectivePlaneRealization)
      (minimalHopfCollapsedAttachingPushoutToProjectivePlane.hom.comp
        minimalHopfProjectivePlaneToCollapsedAttachingPushout.hom) where
  toFun p := minimalHopfCollapsedAttachingProjectivePlanePath p.2 p.1
  continuous_toFun := minimalHopfCollapsedAttachingProjectivePlanePath.hom.uncurry.continuous.comp
    (continuous_snd.prodMk continuous_fst)
  map_zero_left x := by
    exact ConcreteCategory.congr_hom minimalHopfCollapsedAttachingProjectivePlanePath_zero x
  map_one_left x := by
    exact ConcreteCategory.congr_hom minimalHopfCollapsedAttachingProjectivePlanePath_one x

noncomputable def minimalHopfCollapsedAttachingTargetHomotopyForward :
    ContinuousMap.Homotopy
      minimalHopfCollapsedAttachingPushoutTargetIncl.hom
      minimalHopfCollapsedAttachingPushoutTargetIncl.hom :=
  ContinuousMap.Homotopy.refl _

noncomputable def minimalHopfCollapsedAttachingSimplexHomotopyForward :
    ContinuousMap.Homotopy
      minimalHopfCollapsedAttachingPushoutSimplexIncl.hom
      (minimalHopfProjectivePlaneToCollapsedAttachingPushout.hom.comp
        minimalHopfCollapsedAttachingAdjustedSimplexMap.hom) := by
  let Hraw := (ContinuousMap.Homotopy.refl
    minimalHopfProjectivePlaneToCollapsedAttachingPushout.hom).comp
      minimalHopfCollapsedAttachingSimplexToProjectivePlaneHomotopyForward
  have hstart :
      minimalHopfProjectivePlaneToCollapsedAttachingPushout.hom.comp
          (SSet.toTop.map
            minimalHopfProjectivePlaneInteriorSimplexSSetIncl).hom =
        minimalHopfCollapsedAttachingPushoutSimplexIncl.hom := by
    apply ContinuousMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      minimalHopfProjectivePlaneInteriorSimplexIncl_toCollapsedAttachingPushout x
  exact Hraw.cast hstart rfl

noncomputable def minimalHopfCollapsedAttachingTargetHomotopyForwardCurried :
    SSet.toTop.obj (orderedSSet minimalHopfTargetFacets) ⟶
      TopCat.of C(I, minimalHopfCollapsedAttachingPushout) :=
  TopCat.ofHom minimalHopfCollapsedAttachingTargetHomotopyForward.toContinuousMap.argSwap.curry

noncomputable def minimalHopfCollapsedAttachingSimplexHomotopyForwardCurried :
    SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlaneInteriorSimplexFacets) ⟶
      TopCat.of C(I, minimalHopfCollapsedAttachingPushout) :=
  TopCat.ofHom minimalHopfCollapsedAttachingSimplexHomotopyForward.toContinuousMap.argSwap.curry

theorem minimalHopfCollapsedAttachingPushoutForwardHomotopies_boundary :
    minimalHopfProjectivePlaneTargetAttachingMap ≫
        minimalHopfCollapsedAttachingTargetHomotopyForwardCurried =
      SSet.toTop.map
          minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex ≫
        minimalHopfCollapsedAttachingSimplexHomotopyForwardCurried := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro t
  change minimalHopfCollapsedAttachingPushoutTargetIncl
      (minimalHopfProjectivePlaneTargetAttachingMap x) =
    minimalHopfProjectivePlaneToCollapsedAttachingPushout
      (minimalHopfCollapsedAttachingSimplexToProjectivePlaneHomotopyForward (t,
        SSet.toTop.map
          minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex x))
  have hwall := ConcreteCategory.congr_hom minimalHopfCollapsedAttachingSimplexPathExtension_boundary x
  apply_fun fun path ↦ path t at hwall
  change minimalHopfCollapsedAttachingSimplexPathExtension
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex x) t =
    minimalHopfCollapsedAttachingBoundaryHomotopy (t, x) at hwall
  change minimalHopfCollapsedAttachingPushoutTargetIncl
      (minimalHopfProjectivePlaneTargetAttachingMap x) =
    minimalHopfProjectivePlaneToCollapsedAttachingPushout
      (minimalHopfCollapsedAttachingSimplexPathExtension
        (SSet.toTop.map
          minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex x) t)
  rw [hwall]
  have hp := ConcreteCategory.congr_hom
    minimalHopfProjectivePlanePuncturedIncl_toCollapsedAttachingPushout
      (minimalHopfProjectivePlanePuncturedRealizationDeformation.symm
        (t, SSet.toTop.map
          minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured x))
  rw [ConcreteCategory.comp_apply] at hp
  change minimalHopfCollapsedAttachingPushoutTargetIncl
      (minimalHopfProjectivePlaneTargetAttachingMap x) =
    minimalHopfProjectivePlaneToCollapsedAttachingPushout
      (SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl
        (minimalHopfProjectivePlanePuncturedRealizationDeformation.symm
          (t, SSet.toTop.map
            minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured x)))
  rw [hp]
  simp only [ConcreteCategory.comp_apply]
  apply congrArg minimalHopfCollapsedAttachingPushoutTargetIncl
  change minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured x) =
    minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun
      (minimalHopfProjectivePlanePuncturedRealizationDeformation.symm
        (t, SSet.toTop.map
          minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured x))
  exact (minimalHopfProjectivePlanePuncturedRealizationDeformation_invFun
    (σ t)
    (SSet.toTop.map
      minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured x)).symm

theorem minimalHopfCollapsedAttachingTargetToProjectivePlane_eq_targetIncl :
    minimalHopfCollapsedAttachingTargetToProjectivePlane =
      SSet.toTop.map minimalHopfTargetSSetIncl := by
  apply TopCat.hom_ext
  change (SSet.toTop.map
      minimalHopfProjectivePlanePuncturedSSetIncl).hom.comp
      minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.toFun = _
  rw [minimalHopfTargetRealizationInclPuncturedHomotopyEquiv_toFun]
  have hcat :
      SSet.toTop.map minimalHopfTargetSSetInclPunctured ≫
          SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl =
        SSet.toTop.map minimalHopfTargetSSetIncl := by
    rw [← SSet.toTop.map_comp,
      minimalHopfTargetSSetInclPunctured_comp_projectivePlanePuncturedSSetIncl]
  exact congrArg ConcreteCategory.hom hcat

noncomputable def minimalHopfCollapsedAttachingPushoutPath :
    minimalHopfCollapsedAttachingPushout ⟶
      TopCat.of C(I, minimalHopfCollapsedAttachingPushout) :=
  minimalHopfCollapsedAttachingPushout_isPushout.desc
    minimalHopfCollapsedAttachingTargetHomotopyForwardCurried
    minimalHopfCollapsedAttachingSimplexHomotopyForwardCurried
    minimalHopfCollapsedAttachingPushoutForwardHomotopies_boundary

@[reassoc]
theorem minimalHopfCollapsedAttachingPushoutPath_target :
    minimalHopfCollapsedAttachingPushoutTargetIncl ≫
        minimalHopfCollapsedAttachingPushoutPath =
      minimalHopfCollapsedAttachingTargetHomotopyForwardCurried := by
  apply minimalHopfCollapsedAttachingPushout_isPushout.inl_desc

@[reassoc]
theorem minimalHopfCollapsedAttachingPushoutPath_simplex :
    minimalHopfCollapsedAttachingPushoutSimplexIncl ≫
        minimalHopfCollapsedAttachingPushoutPath =
      minimalHopfCollapsedAttachingSimplexHomotopyForwardCurried := by
  apply minimalHopfCollapsedAttachingPushout_isPushout.inr_desc

theorem minimalHopfCollapsedAttachingPushoutPath_zero :
    minimalHopfCollapsedAttachingPushoutPath ≫
        PathSpace.eval₀ minimalHopfCollapsedAttachingPushout =
      𝟙 minimalHopfCollapsedAttachingPushout := by
  apply minimalHopfCollapsedAttachingPushout_isPushout.hom_ext
  · rw [← Category.assoc, minimalHopfCollapsedAttachingPushoutPath_target]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact minimalHopfCollapsedAttachingTargetHomotopyForward.apply_zero x
  · rw [← Category.assoc, minimalHopfCollapsedAttachingPushoutPath_simplex]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact minimalHopfCollapsedAttachingSimplexHomotopyForward.apply_zero x

theorem minimalHopfCollapsedAttachingPushoutPath_one :
    minimalHopfCollapsedAttachingPushoutPath ≫
        PathSpace.evalAt minimalHopfCollapsedAttachingPushout 1 =
      minimalHopfCollapsedAttachingPushoutToProjectivePlane ≫ minimalHopfProjectivePlaneToCollapsedAttachingPushout := by
  apply minimalHopfCollapsedAttachingPushout_isPushout.hom_ext
  · rw [← Category.assoc, minimalHopfCollapsedAttachingPushoutPath_target]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change minimalHopfCollapsedAttachingTargetHomotopyForward (1, x) =
      minimalHopfProjectivePlaneToCollapsedAttachingPushout
        (minimalHopfCollapsedAttachingPushoutToProjectivePlane (minimalHopfCollapsedAttachingPushoutTargetIncl x))
    rw [ContinuousMap.Homotopy.apply_one]
    have hi := ConcreteCategory.congr_hom minimalHopfCollapsedAttachingInverse_target x
    rw [ConcreteCategory.comp_apply] at hi
    rw [hi, minimalHopfCollapsedAttachingTargetToProjectivePlane_eq_targetIncl]
    exact (ConcreteCategory.congr_hom
      minimalHopfTargetIncl_toCollapsedAttachingPushout x).symm
  · rw [← Category.assoc, minimalHopfCollapsedAttachingPushoutPath_simplex]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change minimalHopfCollapsedAttachingSimplexHomotopyForward (1, x) =
      minimalHopfProjectivePlaneToCollapsedAttachingPushout
        (minimalHopfCollapsedAttachingPushoutToProjectivePlane (minimalHopfCollapsedAttachingPushoutSimplexIncl x))
    rw [ContinuousMap.Homotopy.apply_one]
    have hi := ConcreteCategory.congr_hom minimalHopfCollapsedAttachingInverse_simplex x
    rw [ConcreteCategory.comp_apply] at hi
    rw [hi]
    rfl

noncomputable def minimalHopfCollapsedAttachingPushoutHomotopyForward :
    ContinuousMap.Homotopy
      (ContinuousMap.id minimalHopfCollapsedAttachingPushout)
      (minimalHopfProjectivePlaneToCollapsedAttachingPushout.hom.comp
        minimalHopfCollapsedAttachingPushoutToProjectivePlane.hom) where
  toFun p := minimalHopfCollapsedAttachingPushoutPath p.2 p.1
  continuous_toFun := minimalHopfCollapsedAttachingPushoutPath.hom.uncurry.continuous.comp
    (continuous_snd.prodMk continuous_fst)
  map_zero_left x := by
    exact ConcreteCategory.congr_hom minimalHopfCollapsedAttachingPushoutPath_zero x
  map_one_left x := by
    exact ConcreteCategory.congr_hom minimalHopfCollapsedAttachingPushoutPath_one x

noncomputable def minimalHopfProjectivePlaneToCollapsedAttachingPushoutHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      projectivePlaneRealization minimalHopfCollapsedAttachingPushout where
  toFun := minimalHopfProjectivePlaneToCollapsedAttachingPushout.hom
  invFun := minimalHopfCollapsedAttachingPushoutToProjectivePlane.hom
  left_inv := ⟨minimalHopfCollapsedAttachingProjectivePlaneHomotopyForward.symm⟩
  right_inv := ⟨minimalHopfCollapsedAttachingPushoutHomotopyForward.symm⟩

theorem minimalHopfProjectivePlaneToCollapsedAttachingPushoutHomotopyEquiv_toFun :
    minimalHopfProjectivePlaneToCollapsedAttachingPushoutHomotopyEquiv.toFun =
      minimalHopfProjectivePlaneToCollapsedAttachingPushout.hom :=
  rfl

theorem minimalHopfProjectivePlaneToCollapsedAttachingPushoutHomotopyEquiv_invFun :
    minimalHopfProjectivePlaneToCollapsedAttachingPushoutHomotopyEquiv.invFun =
      minimalHopfCollapsedAttachingPushoutToProjectivePlane.hom :=
  rfl

end Submission.ComplexProjectivePlaneTriangulation
