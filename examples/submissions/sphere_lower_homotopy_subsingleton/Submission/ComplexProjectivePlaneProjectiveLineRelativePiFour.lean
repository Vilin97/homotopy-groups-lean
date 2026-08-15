/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneProjectiveLinePairConnectivity

/-!
# The first nonzero relative homotopy group of `(CP², CP¹)`

The literal embedded pair `(CP², CP¹)` is exactly three-connected.  Its first possible
nonzero relative group is therefore `π₄`.  The long exact sequence identifies its boundary
map with an isomorphism onto `π₃(CP¹)`: both adjacent ambient groups `π₄(CP²)` and `π₃(CP²)`
vanish.  Since `π₃(CP¹) = ℤ`, this computes

`π₄(CP², CP¹) ≃ ℤ`.

The construction is uniform in the subspace basepoint.  A second exact equivalence records the
same computation directly for the literal range of the finite four-triangle comparison map.
-/

open CategoryTheory
open scoped Topology Topology.Homotopy TopCat

noncomputable section

namespace Submission

universe u

/-! ## General relative-fourth-group comparison -/

/-- When the adjacent ambient groups vanish, the degree-four relative boundary is a
multiplicative equivalence onto the third homotopy group of the subspace. -/
noncomputable def RelHomotopyGroup.bdPiFourMulEquivOfAmbientSubsingleton
    {Y : Type*} [TopologicalSpace Y] {A : Set Y} (a : A)
    (hfour : Subsingleton (π_ 4 Y (a : Y)))
    (hthree : Subsingleton (π_ 3 Y (a : Y))) :
    RelHomotopyGroup 4 Y A a ≃* π_ 3 A a :=
  MulEquiv.ofBijective (RelHomotopyGroup.bdHom 2 Y A a)
    (bijective_bd_of_subsingleton 2 a hfour hthree)

/-- For an embedded range, the degree-four relative group is identified with the source's
third homotopy group whenever the adjacent target groups vanish. -/
noncomputable def RelHomotopyGroup.rangePiFourMulEquivOfAmbientSubsingleton
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : Topology.IsEmbedding f) (x : X)
    (hfour : Subsingleton (π_ 4 Y (f x)))
    (hthree : Subsingleton (π_ 3 Y (f x))) :
    RelHomotopyGroup 4 Y (Set.range f) (hf.toHomeomorph x) ≃* π_ 3 X x :=
  (RelHomotopyGroup.bdPiFourMulEquivOfAmbientSubsingleton
      (hf.toHomeomorph x) hfour hthree).trans
    (HomotopyGroup.homeomorphMulEquivOfEq
      (N := Fin 3) hf.toHomeomorph rfl).symm

/-! ## Vanishing of the adjacent ambient group -/

/-- The geometric complex projective plane has trivial fourth homotopy group at every
basepoint. -/
theorem piFour_complexProjectivePlane_subsingleton_at
    (x : ComplexProjectiveModel 2) :
    Subsingleton (π_ 4 (ComplexProjectiveModel 2) x) := by
  letI : PathConnectedSpace (ComplexProjectiveModel 2) :=
    pathConnectedSpace_complexProjectiveModel 2
  obtain ⟨changeBasepoint⟩ := nonempty_mulEquiv_of_pathConnectedSpace
    (N := Fin 4) x (complexProjectiveModelBasepoint 2)
  obtain ⟨changeSpace⟩ :=
    complexProjectiveModel_higher_homotopy_mulEquiv_sphere 2 1 (by omega)
  exact (changeBasepoint.trans changeSpace).toEquiv.subsingleton_congr.mpr
    (subsingleton_homotopyGroup_sphere_of_lt 4 5 (by omega)
      (sphereBasepoint 5))

/-! ## The literal embedded pair -/

/-- The literal embedded projective line is path connected. -/
noncomputable instance complexProjectivePlaneProjectiveLinePathConnectedSpace :
    PathConnectedSpace complexProjectivePlaneProjectiveLine := by
  letI : PathConnectedSpace (ComplexProjectiveModel 1) :=
    pathConnectedSpace_complexProjectiveModel 1
  exact complexProjectivePlaneProjectiveLineHomeomorph.surjective.pathConnectedSpace
    complexProjectivePlaneProjectiveLineHomeomorph.continuous

/-- At every basepoint, the literal projective line has infinite cyclic third homotopy
group. -/
noncomputable def complexProjectivePlaneProjectiveLinePiThreeMulEquivIntAt
    (a : complexProjectivePlaneProjectiveLine) :
    π_ 3 complexProjectivePlaneProjectiveLine a ≃* Multiplicative ℤ :=
  (Classical.choice (nonempty_mulEquiv_of_pathConnectedSpace
      (N := Fin 3) a complexProjectivePlaneProjectiveLineBasepoint)).trans
    complexProjectivePlaneProjectiveLinePiThreeMulEquivInt

/-- The relative-fourth-group boundary of the literal pair is bijective at every
basepoint. -/
theorem complexProjectivePlaneProjectiveLine_relative_piFour_boundary_bijective
    (a : complexProjectivePlaneProjectiveLine) :
    Function.Bijective
      (RelHomotopyGroup.bd 3 (ComplexProjectiveModel 2)
        complexProjectivePlaneProjectiveLine a) :=
  bijective_bd_of_subsingleton 2 a
    (piFour_complexProjectivePlane_subsingleton_at (a : ComplexProjectiveModel 2))
    (piThree_complexProjectivePlane_subsingleton_at (a : ComplexProjectiveModel 2))

/-- The relative-fourth-group boundary of the literal pair as a multiplicative
equivalence. -/
noncomputable def complexProjectivePlaneProjectiveLineRelativePiFourBoundaryMulEquiv
    (a : complexProjectivePlaneProjectiveLine) :
    RelHomotopyGroup 4 (ComplexProjectiveModel 2)
        complexProjectivePlaneProjectiveLine a ≃*
      π_ 3 complexProjectivePlaneProjectiveLine a :=
  MulEquiv.ofBijective
    (RelHomotopyGroup.bdHom 2 (ComplexProjectiveModel 2)
      complexProjectivePlaneProjectiveLine a)
    (complexProjectivePlaneProjectiveLine_relative_piFour_boundary_bijective a)

/-- At every projective-line basepoint, the literal pair has relative `π₄ = ℤ`. -/
noncomputable def complexProjectivePlaneProjectiveLineRelativePiFourMulEquivIntAt
    (a : complexProjectivePlaneProjectiveLine) :
    RelHomotopyGroup 4 (ComplexProjectiveModel 2)
        complexProjectivePlaneProjectiveLine a ≃* Multiplicative ℤ :=
  (complexProjectivePlaneProjectiveLineRelativePiFourBoundaryMulEquiv a).trans
    (complexProjectivePlaneProjectiveLinePiThreeMulEquivIntAt a)

/-- Relative `π₄(CP², CP¹)` is infinite at every subspace basepoint. -/
theorem complexProjectivePlaneProjectiveLine_relative_piFour_infinite_at
    (a : complexProjectivePlaneProjectiveLine) :
    Infinite
      (RelHomotopyGroup 4 (ComplexProjectiveModel 2)
        complexProjectivePlaneProjectiveLine a) := by
  let e := complexProjectivePlaneProjectiveLineRelativePiFourMulEquivIntAt a
  exact Infinite.of_injective e.symm e.symm.injective

/-! ## The literal finite-comparison range -/

namespace ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The finite projective-line comparison is an embedding in the exact form used for its
range homeomorphism. -/
theorem projectiveLineRealizationToComplexProjectivePlane_isEmbedding :
    Topology.IsEmbedding projectiveLineRealizationToComplexProjectivePlane.hom :=
  projectiveLineRealizationToComplexProjectivePlane_isClosedEmbedding.isEmbedding

/-- The maintained basepoint in the literal range of the finite projective-line
comparison. -/
noncomputable def projectiveLineRealizationToComplexProjectivePlaneRangeBasepoint :
    Set.range projectiveLineRealizationToComplexProjectivePlane.hom :=
  projectiveLineRealizationToComplexProjectivePlane_isEmbedding.toHomeomorph
    projectiveLineBasepoint

/-- The literal finite-comparison range basepoint is the maintained basepoint of geometric
`CP²`. -/
@[simp]
theorem projectiveLineRealizationToComplexProjectivePlaneRangeBasepoint_coe :
    (projectiveLineRealizationToComplexProjectivePlaneRangeBasepoint :
      ComplexProjectiveModel 2) = complexProjectiveModelBasepoint 2 :=
  projectiveLineRealizationToComplexProjectivePlane_basepoint

/-- The first nonzero relative homotopy group of the finite comparison range is exactly the
integers. -/
noncomputable def
    projectiveLineRealizationToComplexProjectivePlaneRangeRelativePiFourMulEquivInt :
    RelHomotopyGroup 4 (ComplexProjectiveModel 2)
        (Set.range projectiveLineRealizationToComplexProjectivePlane.hom)
        projectiveLineRealizationToComplexProjectivePlaneRangeBasepoint ≃*
      Multiplicative ℤ :=
  (RelHomotopyGroup.rangePiFourMulEquivOfAmbientSubsingleton
      projectiveLineRealizationToComplexProjectivePlane.hom
      projectiveLineRealizationToComplexProjectivePlane_isEmbedding
      projectiveLineBasepoint
      (piFour_complexProjectivePlane_subsingleton_at _)
      (piThree_complexProjectivePlane_subsingleton_at _)).trans
    (Classical.choice projectiveLinePiThree_mulEquiv_int)

/-- Relative `π₄` of the literal finite-comparison range is infinite. -/
theorem projectiveLineRealizationToComplexProjectivePlaneRange_relative_piFour_infinite :
    Infinite
      (RelHomotopyGroup 4 (ComplexProjectiveModel 2)
        (Set.range projectiveLineRealizationToComplexProjectivePlane.hom)
        projectiveLineRealizationToComplexProjectivePlaneRangeBasepoint) := by
  let e :=
    projectiveLineRealizationToComplexProjectivePlaneRangeRelativePiFourMulEquivInt
  exact Infinite.of_injective e.symm e.symm.injective

end ComplexProjectivePlaneTriangulation

end Submission
