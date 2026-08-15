/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTriangulationProjectiveLineComparison
import Submission.Homotopy.FibrationLESNaturality

/-!
# The projective-line inclusion on second homotopy groups

The standard coordinate inclusions form a commuting square between the complex Hopf fibrations
over `CP¹` and `CP²`.  On the basepoint fibres this square is the identity in the common circle
coordinate.  Naturality of the connecting maps therefore proves that the actual inclusion
`CP¹ ↪ CP²` induces an isomorphism on `π₂`.

Composing with the maintained homeomorphism from the four-triangle projective-line realization
to `CP¹` proves the corresponding statement for the finite-to-geometric comparison map.
-/

open CategoryTheory
open scoped Topology Topology.Homotopy TopCat

noncomputable section

namespace Submission

/-- Adding a final zero coordinate preserves the Euclidean norm. -/
theorem norm_complexProjectivePlaneBottomInclVec
    (w : ComplexEuclidean 1) :
    ‖complexProjectivePlaneBottomInclVec w‖ = ‖w‖ := by
  simp [complexProjectivePlaneBottomInclVec, EuclideanSpace.norm_eq,
    Fin.sum_univ_succ]

/-- The coordinate inclusion of the unit three-sphere into the unit five-sphere. -/
noncomputable def complexUnitSphereBottomIncl
    (z : ComplexUnitSphere 1) : ComplexUnitSphere 2 :=
  ⟨complexProjectivePlaneBottomInclVec z, by
    rw [Metric.mem_sphere, dist_zero_right,
      norm_complexProjectivePlaneBottomInclVec,
      norm_coe_complexUnitSphere]⟩

/-- The coordinate inclusion of complex unit spheres is continuous. -/
theorem continuous_complexUnitSphereBottomIncl :
    Continuous complexUnitSphereBottomIncl :=
  Continuous.subtype_mk
    (continuous_complexProjectivePlaneBottomInclVec.comp continuous_subtype_val) _

/-- The coordinate inclusion of complex unit spheres as a continuous map. -/
noncomputable def complexUnitSphereBottomInclMap :
    C(ComplexUnitSphere 1, ComplexUnitSphere 2) :=
  ⟨complexUnitSphereBottomIncl, continuous_complexUnitSphereBottomIncl⟩

/-- The standard bottom-projective-line inclusion as a continuous map. -/
noncomputable def complexProjectivePlaneBottomInclMap :
    C(ComplexProjectiveModel 1, ComplexProjectiveModel 2) :=
  ⟨complexProjectivePlaneBottomIncl,
    continuous_complexProjectivePlaneBottomIncl⟩

/-- The continuous bottom-projective-line inclusion preserves the maintained basepoints. -/
@[simp]
theorem complexProjectivePlaneBottomInclMap_basepoint :
    complexProjectivePlaneBottomInclMap (complexProjectiveModelBasepoint 1) =
      complexProjectiveModelBasepoint 2 :=
  complexProjectivePlaneBottomIncl_basepoint

/-- The coordinate inclusion of complex unit spheres preserves the maintained basepoints. -/
@[simp]
theorem complexUnitSphereBottomIncl_basepoint :
    complexUnitSphereBottomIncl (complexUnitSphereBasepoint 1) =
      complexUnitSphereBasepoint 2 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [complexUnitSphereBottomIncl, complexProjectivePlaneBottomInclVec,
      complexUnitSphereBasepoint]

/-- The coordinate inclusions commute with the complex Hopf maps. -/
theorem complexHopfMap_bottomIncl :
    (complexHopfMap 2).comp complexUnitSphereBottomInclMap =
      complexProjectivePlaneBottomInclMap.comp (complexHopfMap 1) := by
  apply ContinuousMap.ext
  intro z
  change Projectivization.mk ℂ
      (complexProjectivePlaneBottomInclVec (z : ComplexEuclidean 1)) _ =
    complexProjectivePlaneBottomIncl
      (Projectivization.mk ℂ (z : ComplexEuclidean 1) _)
  rw [complexProjectivePlaneBottomIncl_mk]

/-- The map of fibre pairs obtained from the commuting square of complex Hopf fibrations. -/
noncomputable abbrev complexHopfBottomPairMap :=
  fibrationBasedPairMap
    (complexHopfFiberBasepoint 1) (complexHopfFiberBasepoint 2)
    complexUnitSphereBottomInclMap complexProjectivePlaneBottomInclMap
    complexUnitSphereBottomIncl_basepoint
    complexProjectivePlaneBottomInclMap_basepoint complexHopfMap_bottomIncl

/-- The induced map of basepoint Hopf fibres is the canonical circle-coordinate
homeomorphism. -/
noncomputable def complexHopfFiberBottomHomeomorph :
    ComplexHopfFiber 1 ≃ₜ ComplexHopfFiber 2 :=
  (circleHomeomorphComplexHopfFiber 1).symm.trans
    (circleHomeomorphComplexHopfFiber 2)

/-- The circle-coordinate homeomorphism between the Hopf fibres preserves basepoints. -/
@[simp]
theorem complexHopfFiberBottomHomeomorph_basepoint :
    complexHopfFiberBottomHomeomorph (complexHopfFiberBasepoint 1) =
      complexHopfFiberBasepoint 2 := by
  have hcircle :
      (circleHomeomorphComplexHopfFiber 1).symm
          (complexHopfFiberBasepoint 1) = 1 := by
    apply (circleHomeomorphComplexHopfFiber 1).injective
    rw [(circleHomeomorphComplexHopfFiber 1).apply_symm_apply,
      circleHomeomorphComplexHopfFiber_one]
  change (circleHomeomorphComplexHopfFiber 2)
      ((circleHomeomorphComplexHopfFiber 1).symm
        (complexHopfFiberBasepoint 1)) = _
  rw [hcircle, circleHomeomorphComplexHopfFiber_one]

/-- The fibre map supplied by the commuting Hopf square is the circle-coordinate
homeomorphism. -/
theorem complexHopfBottomPairMap_subspaceMap :
    complexHopfBottomPairMap.subspaceMap =
      ⟨complexHopfFiberBottomHomeomorph,
        complexHopfFiberBottomHomeomorph.continuous⟩ := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨c, hc⟩ := complexHopfFiber_vector_eq 1 z
  apply Subtype.ext
  change complexUnitSphereBottomIncl (z : ComplexUnitSphere 1) =
    (complexCircleToHopfFiber 2 (complexHopfFiberToCircle 1 z) :
      ComplexUnitSphere 2)
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · rfl
  · have hcoord := congrArg (fun v : ComplexEuclidean 1 => v 1) hc
    change ((z : ComplexUnitSphere 1) : ComplexEuclidean 1) 1 = 0
    simpa using hcoord.symm
  · rfl

/-- The degree-two connecting map of every positive-dimensional complex Hopf fibration is
bijective. -/
theorem complexHopfFibDeltaPiTwo_bijective (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective
      (fibDelta (complexHopfFiberBasepoint n)
        (complexHopfMap_isSerreFibration n) 1) := by
  have h₂ : Subsingleton
      (π_ 2 (ComplexUnitSphere n) (complexUnitSphereBasepoint n)) :=
    complexUnitSphere_positive_lower_homotopy_subsingleton n 1 (by omega)
  have h₁ : Subsingleton
      (π_ 1 (ComplexUnitSphere n) (complexUnitSphereBasepoint n)) :=
    complexUnitSphere_positive_lower_homotopy_subsingleton n 0 (by omega)
  exact (fibDeltaMulEquiv (complexHopfFiberBasepoint n)
    (complexHopfMap_isSerreFibration n) 0 h₂ h₁).bijective

/-- The coordinate inclusion induces an isomorphism on the fundamental groups of the Hopf
fibres. -/
theorem complexHopfBottomFiber_piOne_bijective :
    Function.Bijective
      (HomotopyGroup.map (N := Fin 1)
        complexHopfBottomPairMap.subspaceMap
        complexHopfBottomPairMap.subspaceMap_basepoint) := by
  let homeoMap : C(ComplexHopfFiber 1, ComplexHopfFiber 2) :=
    ⟨complexHopfFiberBottomHomeomorph,
      complexHopfFiberBottomHomeomorph.continuous⟩
  have hmap : complexHopfBottomPairMap.subspaceMap = homeoMap :=
    complexHopfBottomPairMap_subspaceMap
  have hinduced :
      (HomotopyGroup.map (N := Fin 1)
        complexHopfBottomPairMap.subspaceMap
        complexHopfBottomPairMap.subspaceMap_basepoint) =
      HomotopyGroup.map homeoMap
        complexHopfFiberBottomHomeomorph_basepoint := by
    funext z
    exact HomotopyGroup.map_congr hmap _ _ z
  rw [hinduced]
  exact (HomotopyGroup.homeomorphMulEquivOfEq
    (N := Fin 1) complexHopfFiberBottomHomeomorph
    complexHopfFiberBottomHomeomorph_basepoint).bijective

/-- The standard inclusion `CP¹ ↪ CP²` induces a bijection on second homotopy groups. -/
theorem complexProjectivePlaneBottomIncl_piTwo_bijective :
    Function.Bijective
      (HomotopyGroup.map (N := Fin 2)
        complexProjectivePlaneBottomInclMap
        complexProjectivePlaneBottomInclMap_basepoint) :=
  homotopyGroup_map_bijective_of_fibDelta
    (complexHopfFiberBasepoint 1) (complexHopfFiberBasepoint 2)
    (complexHopfMap_isSerreFibration 1) (complexHopfMap_isSerreFibration 2)
    complexUnitSphereBottomInclMap complexProjectivePlaneBottomInclMap
    complexUnitSphereBottomIncl_basepoint
    complexProjectivePlaneBottomInclMap_basepoint complexHopfMap_bottomIncl 1
    (complexHopfFibDeltaPiTwo_bijective 1 (by omega))
    (complexHopfFibDeltaPiTwo_bijective 2 (by omega))
    complexHopfBottomFiber_piOne_bijective

/-- The exact multiplicative equivalence on `π₂` induced by `CP¹ ↪ CP²`. -/
noncomputable def complexProjectivePlaneBottomInclPiTwoMulEquiv :
    π_ 2 (ComplexProjectiveModel 1) (complexProjectiveModelBasepoint 1) ≃*
      π_ 2 (ComplexProjectiveModel 2) (complexProjectiveModelBasepoint 2) :=
  MulEquiv.ofBijective
    (HomotopyGroup.mapHom (N := Fin 2)
      complexProjectivePlaneBottomInclMap
      complexProjectivePlaneBottomInclMap_basepoint)
    complexProjectivePlaneBottomIncl_piTwo_bijective

namespace ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The finite projective-line comparison with geometric `CP²` induces a bijection on `π₂`. -/
theorem projectiveLineRealizationToComplexProjectivePlane_piTwo_bijective :
    Function.Bijective
      (HomotopyGroup.map (N := Fin 2)
        projectiveLineRealizationToComplexProjectivePlane.hom
        projectiveLineRealizationToComplexProjectivePlane_basepoint) := by
  let lineMap : C(SSet.toTop.obj (orderedSSet projectiveLineCycle),
      ComplexProjectiveModel 1) :=
    ⟨projectiveLineRealizationHomeomorphComplexProjectiveLine,
      projectiveLineRealizationHomeomorphComplexProjectiveLine.continuous⟩
  have hline : Function.Bijective
      (HomotopyGroup.map (N := Fin 2) lineMap
        projectiveLineRealizationHomeomorphComplexProjectiveLine_basepoint) :=
    (HomotopyGroup.homeomorphMulEquivOfEq
      (N := Fin 2) projectiveLineRealizationHomeomorphComplexProjectiveLine
      projectiveLineRealizationHomeomorphComplexProjectiveLine_basepoint).bijective
  have hcomp := complexProjectivePlaneBottomIncl_piTwo_bijective.comp hline
  have hmap :
      (HomotopyGroup.map (N := Fin 2)
        projectiveLineRealizationToComplexProjectivePlane.hom
        projectiveLineRealizationToComplexProjectivePlane_basepoint) =
      fun z => HomotopyGroup.map
          complexProjectivePlaneBottomInclMap
          complexProjectivePlaneBottomInclMap_basepoint
          (HomotopyGroup.map lineMap
            projectiveLineRealizationHomeomorphComplexProjectiveLine_basepoint z) := by
    funext z
    rw [HomotopyGroup.map_comp_apply]
    rfl
  rw [hmap]
  exact hcomp

/-- The exact `π₂` equivalence induced by the finite-projective-line comparison with `CP²`. -/
noncomputable def projectiveLineRealizationToComplexProjectivePlanePiTwoMulEquiv :
    π_ 2 (SSet.toTop.obj (orderedSSet projectiveLineCycle)) projectiveLineBasepoint ≃*
      π_ 2 (ComplexProjectiveModel 2) (complexProjectiveModelBasepoint 2) :=
  MulEquiv.ofBijective
    (HomotopyGroup.mapHom (N := Fin 2)
      projectiveLineRealizationToComplexProjectivePlane.hom
      projectiveLineRealizationToComplexProjectivePlane_basepoint)
    projectiveLineRealizationToComplexProjectivePlane_piTwo_bijective

end ComplexProjectivePlaneTriangulation

end Submission
