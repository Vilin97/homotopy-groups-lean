/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneCohomology
import Submission.ComplexProjectivePlaneTriangulationProjectiveLine

/-!
# Comparing the finite projective line with the bottom cell of geometric CP²

The four-triangle sphere inside the nine-vertex complex has already been identified with the
maintained quotient-topology `CP¹`.  Composing that homeomorphism with the standard bottom-cell
inclusion gives a canonical comparison map from the finite realization to geometric `CP²`.

This file proves that the comparison is a basepoint-preserving closed embedding and that its
range is exactly the standard projective line.  The normalized geometric degree-two class pulls
back to a nonzero singular class, proving both the standard bottom inclusion and the finite
comparison map are not nullhomotopic.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped Topology TopCat

namespace Submission

/-- The normalized mod-two singular cohomology class on the projective line. -/
noncomputable def complexProjectiveLineModTwoClass :
    Hsing 2 (TopCat.of (ComplexProjectiveModel 1)) (ZMod 2) :=
  Hsing.map complexProjectiveLineIsoSphereTwo.hom 2
    (sphereTopModTwoClass 1)

/-- The normalized mod-two class on the projective line is nonzero. -/
theorem complexProjectiveLineModTwoClass_ne_zero :
    complexProjectiveLineModTwoClass ≠ 0 := by
  intro hzero
  apply sphereTopModTwoClass_ne_zero 1
  apply (Hsing.map_bijective_of_isIso (R := ZMod 2)
    complexProjectiveLineIsoSphereTwo.hom 2).1
  simpa [complexProjectiveLineModTwoClass] using hzero

/-- The standard bottom projective line is closed embedded in geometric `CP²`. -/
theorem complexProjectivePlaneBottomIncl_isClosedEmbedding :
    Topology.IsClosedEmbedding complexProjectivePlaneBottomIncl :=
  continuous_complexProjectivePlaneBottomIncl.isClosedEmbedding
    complexProjectivePlaneBottomIncl_injective

/-- The bottom-projective-line inclusion in geometric `CP²` is not nullhomotopic. -/
theorem complexProjectivePlaneBottomIncl_not_nullhomotopic :
    ¬ complexProjectivePlaneBottomInclTopCat.hom.Nullhomotopic := by
  rintro ⟨z, ⟨H⟩⟩
  change TopCat.Homotopy complexProjectivePlaneBottomInclTopCat
    (TopCat.const z) at H
  have hmaps := LinearMap.congr_fun
    (Hsing.map_congr (R := ZMod 2) H 2)
    complexProjectivePlaneModTwoClass
  rw [complexProjectivePlaneModTwoClass_restrict,
    Hsing.map_const_eq_zero (ZMod 2) z 2 (by omega),
    LinearMap.zero_apply] at hmaps
  exact complexProjectiveLineModTwoClass_ne_zero hmaps

namespace ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The recognized finite projective line mapped onto the bottom projective line in geometric
`CP²`. -/
noncomputable def projectiveLineRealizationToComplexProjectivePlane :
    SSet.toTop.obj (orderedSSet projectiveLineCycle) ⟶
      TopCat.of (ComplexProjectiveModel 2) :=
  (TopCat.isoOfHomeo
      projectiveLineRealizationHomeomorphComplexProjectiveLine).hom ≫
    complexProjectivePlaneBottomInclTopCat

@[simp]
theorem projectiveLineRealizationToComplexProjectivePlane_apply
    (x : SSet.toTop.obj (orderedSSet projectiveLineCycle)) :
    projectiveLineRealizationToComplexProjectivePlane x =
      complexProjectivePlaneBottomIncl
        (projectiveLineRealizationHomeomorphComplexProjectiveLine x) :=
  rfl

/-- The finite projective-line comparison preserves the maintained basepoints. -/
@[simp]
theorem projectiveLineRealizationToComplexProjectivePlane_basepoint :
    projectiveLineRealizationToComplexProjectivePlane projectiveLineBasepoint =
      complexProjectiveModelBasepoint 2 := by
  rw [projectiveLineRealizationToComplexProjectivePlane_apply,
    projectiveLineRealizationHomeomorphComplexProjectiveLine_basepoint,
    complexProjectivePlaneBottomIncl_basepoint]

/-- The finite projective-line comparison is injective. -/
theorem projectiveLineRealizationToComplexProjectivePlane_injective :
    Function.Injective projectiveLineRealizationToComplexProjectivePlane :=
  complexProjectivePlaneBottomIncl_injective.comp
    projectiveLineRealizationHomeomorphComplexProjectiveLine.injective

/-- The finite projective line is closed embedded as the bottom cell of geometric `CP²`. -/
theorem projectiveLineRealizationToComplexProjectivePlane_isClosedEmbedding :
    Topology.IsClosedEmbedding projectiveLineRealizationToComplexProjectivePlane := by
  letI : CompactSpace (SSet.toTop.obj (orderedSSet projectiveLineCycle)) :=
    projectiveLineRealizationHomeomorphSphereTwo.symm.compactSpace
  exact projectiveLineRealizationToComplexProjectivePlane.hom.continuous.isClosedEmbedding
    projectiveLineRealizationToComplexProjectivePlane_injective

/-- The finite comparison has exactly the standard bottom-projective-line image in `CP²`. -/
theorem projectiveLineRealizationToComplexProjectivePlane_range :
    Set.range projectiveLineRealizationToComplexProjectivePlane =
      Set.range complexProjectivePlaneBottomIncl := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨projectiveLineRealizationHomeomorphComplexProjectiveLine x, rfl⟩
  · rintro ⟨p, rfl⟩
    refine ⟨projectiveLineRealizationHomeomorphComplexProjectiveLine.symm p, ?_⟩
    rw [projectiveLineRealizationToComplexProjectivePlane_apply,
      projectiveLineRealizationHomeomorphComplexProjectiveLine.apply_symm_apply]

/-- The normalized singular mod-two class on the realized finite projective line. -/
noncomputable def projectiveLineRealizationModTwoClass :
    Hsing 2 (SSet.toTop.obj (orderedSSet projectiveLineCycle)) (ZMod 2) :=
  Hsing.map
    (TopCat.isoOfHomeo
      projectiveLineRealizationHomeomorphComplexProjectiveLine).hom 2
    complexProjectiveLineModTwoClass

/-- The normalized singular class on the finite projective-line realization is nonzero. -/
theorem projectiveLineRealizationModTwoClass_ne_zero :
    projectiveLineRealizationModTwoClass ≠ 0 := by
  intro hzero
  apply complexProjectiveLineModTwoClass_ne_zero
  apply (Hsing.map_bijective_of_isIso (R := ZMod 2)
    (TopCat.isoOfHomeo
      projectiveLineRealizationHomeomorphComplexProjectiveLine).hom 2).1
  simpa [projectiveLineRealizationModTwoClass] using hzero

/-- Pulling the geometric `CP²` class back along the finite comparison gives its normalized
projective-line class. -/
@[simp]
theorem projectiveLineRealizationToComplexProjectivePlane_modTwoClass :
    Hsing.map projectiveLineRealizationToComplexProjectivePlane 2
        complexProjectivePlaneModTwoClass =
      projectiveLineRealizationModTwoClass := by
  rw [projectiveLineRealizationToComplexProjectivePlane,
    Hsing.map_comp, LinearMap.comp_apply,
    complexProjectivePlaneModTwoClass_restrict]
  rfl

/-- The finite projective-line map to geometric `CP²` is not nullhomotopic. -/
theorem projectiveLineRealizationToComplexProjectivePlane_not_nullhomotopic :
    ¬ projectiveLineRealizationToComplexProjectivePlane.hom.Nullhomotopic := by
  rintro ⟨z, ⟨H⟩⟩
  change TopCat.Homotopy projectiveLineRealizationToComplexProjectivePlane
    (TopCat.const z) at H
  have hmaps := LinearMap.congr_fun
    (Hsing.map_congr (R := ZMod 2) H 2)
    complexProjectivePlaneModTwoClass
  rw [projectiveLineRealizationToComplexProjectivePlane_modTwoClass,
    Hsing.map_const_eq_zero (ZMod 2) z 2 (by omega),
    LinearMap.zero_apply] at hmaps
  exact projectiveLineRealizationModTwoClass_ne_zero hmaps

end ComplexProjectivePlaneTriangulation

end Submission
