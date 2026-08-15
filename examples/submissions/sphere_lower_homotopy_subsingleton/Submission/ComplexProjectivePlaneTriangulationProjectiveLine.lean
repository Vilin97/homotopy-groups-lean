/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectiveLine
import Submission.ComplexProjectivePlaneTriangulation
import Submission.Cohomology.FiniteOrderedComplexReindex
import Submission.FiniteOrderedComplexCarrierFunctorial
import Submission.ForMathlib.HomotopyGroup.Homeomorph
import Submission.Model.SphereConnected
import Submission.Pi2SphereTwoGeneric
import Submission.SSetBoundaryRealization

/-!
# The projective line in the nine-vertex projective plane

The four-triangle cycle used by the finite cup-square certificate is exactly the simplicial
boundary of the tetrahedron on vertices `1,2,3,A`.  Its ordered realization is therefore an
exact two-sphere, and hence an exact copy of the quotient-topology complex projective line.  The
four triangles are faces of the nine-vertex projective-plane complex, so this copy comes with a
canonical simplicial and closed topological embedding into that finite model.

The sphere comparison also computes its homotopy groups: it is connected and simply connected,
its second homotopy group is infinite cyclic at every basepoint, and all its homotopy groups are
transported explicitly to those of `S²` and `CP¹`.  Finally, the explicit degree-two class on the
nine-vertex model pulls back to a nonzero class on this embedded projective line.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped Topology

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The four vertices supporting the displayed projective-line cycle. -/
def projectiveLineVertices : Finset Vertex := {0, 1, 2, 5}

/-- The displayed projective-line cycle is exactly the boundary of its abstract tetrahedron. -/
theorem projectiveLineCycle_eq_simplexBoundary :
    projectiveLineCycle = simplexBoundaryFacets projectiveLineVertices := by
  decide

/-- The projective-line tetrahedron has four vertices. -/
theorem projectiveLineVertices_card : projectiveLineVertices.card = 3 + 1 := by
  decide

/-- The ordered projective-line subcomplex is the standard simplicial three-simplex boundary. -/
noncomputable def projectiveLineSSetIsoBoundaryThree :
    orderedSSet projectiveLineCycle ≅ (SSet.boundary 3 : SSet) :=
  SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex projectiveLineCycle_eq_simplexBoundary) ≪≫
    simplexBoundarySSetIso 3 projectiveLineVertices projectiveLineVertices_card

/-- The realization of the four-triangle projective line is the exact metric two-sphere. -/
noncomputable def projectiveLineRealizationHomeomorphSphereTwo :
    SSet.toTop.obj (orderedSSet projectiveLineCycle) ≃ₜ SphereSpace 2 :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso projectiveLineSSetIsoBoundaryThree)).trans
    (boundaryRealizationHomeomorphSphere 2)

/-- The realization of the four-triangle cycle is an exact topological copy of `CP¹`. -/
noncomputable def projectiveLineRealizationHomeomorphComplexProjectiveLine :
    SSet.toTop.obj (orderedSSet projectiveLineCycle) ≃ₜ
      ComplexProjectiveModel 1 :=
  projectiveLineRealizationHomeomorphSphereTwo.trans
    complexProjectiveLineHomeomorphSphere.symm

/-- The canonical basepoint on the realized projective line, transported back from `CP¹`. -/
noncomputable def projectiveLineBasepoint :
    SSet.toTop.obj (orderedSSet projectiveLineCycle) :=
  projectiveLineRealizationHomeomorphComplexProjectiveLine.symm
    (complexProjectiveModelBasepoint 1)

/-- The realized-projective-line/`CP¹` homeomorphism preserves the maintained basepoints. -/
@[simp]
theorem projectiveLineRealizationHomeomorphComplexProjectiveLine_basepoint :
    projectiveLineRealizationHomeomorphComplexProjectiveLine projectiveLineBasepoint =
      complexProjectiveModelBasepoint 1 :=
  projectiveLineRealizationHomeomorphComplexProjectiveLine.apply_symm_apply _

/-- The realized-projective-line/sphere homeomorphism preserves the maintained basepoints. -/
@[simp]
theorem projectiveLineRealizationHomeomorphSphereTwo_basepoint :
    projectiveLineRealizationHomeomorphSphereTwo projectiveLineBasepoint =
      sphereBasepoint 2 := by
  simp [projectiveLineBasepoint,
    projectiveLineRealizationHomeomorphComplexProjectiveLine]

/-- Every displayed projective-line triangle is a face of the nine-vertex complex. -/
theorem projectiveLineCycle_le_facets :
    FacetFamilyLE projectiveLineCycle facets := by
  unfold FacetFamilyLE IsFace
  decide

/-- The canonical simplicial inclusion of the projective line into the nine-vertex complex. -/
def projectiveLineSSetIncl :
    orderedSSet projectiveLineCycle ⟶ projectivePlaneSSet :=
  orderedSSetHomOfFacetFamilyLE projectiveLineCycle_le_facets

/-- The projective-line simplicial map is a monomorphism. -/
instance projectiveLineSSetIncl_mono : Mono projectiveLineSSetIncl := by
  dsimp [projectiveLineSSetIncl, orderedSSetHomOfFacetFamilyLE]
  infer_instance

/-- The realized projective-line inclusion into the nine-vertex projective-plane model. -/
noncomputable def projectiveLineRealizationIncl :
    SSet.toTop.obj (orderedSSet projectiveLineCycle) ⟶ projectivePlaneRealization :=
  SSet.toTop.map projectiveLineSSetIncl

/-- The realized projective-line inclusion is injective. -/
theorem projectiveLineRealizationIncl_injective :
    Function.Injective projectiveLineRealizationIncl :=
  orderedRealizationMapOfFacetFamilyLE_injective projectiveLineCycle_le_facets

/-- The realized projective line is a closed embedded copy of `S²` inside the finite model. -/
theorem projectiveLineRealizationIncl_isClosedEmbedding :
    Topology.IsClosedEmbedding projectiveLineRealizationIncl :=
  orderedRealizationMapOfFacetFamilyLE_isClosedEmbedding
    projectiveLineCycle_le_facets

/-- The projective-line realization is path connected. -/
noncomputable instance projectiveLineRealizationPathConnectedSpace :
    PathConnectedSpace (SSet.toTop.obj (orderedSSet projectiveLineCycle)) :=
  projectiveLineRealizationHomeomorphSphereTwo.symm.surjective.pathConnectedSpace
    projectiveLineRealizationHomeomorphSphereTwo.symm.continuous

/-- The projective-line realization has one path component at every basepoint. -/
theorem projectiveLinePiZero_subsingleton
    (x : SSet.toTop.obj (orderedSSet projectiveLineCycle)) :
    Subsingleton (π_ 0 (SSet.toTop.obj (orderedSSet projectiveLineCycle)) x) :=
  subsingleton_piZero x

/-- The projective-line realization is simply connected at every basepoint. -/
theorem projectiveLinePiOne_subsingleton
    (x : SSet.toTop.obj (orderedSSet projectiveLineCycle)) :
    Subsingleton (π_ 1 (SSet.toTop.obj (orderedSSet projectiveLineCycle)) x) := by
  let e : π_ 1 (SSet.toTop.obj (orderedSSet projectiveLineCycle)) x ≃
      π_ 1 (SphereSpace 2) (projectiveLineRealizationHomeomorphSphereTwo x) :=
    HomotopyGroup.homeomorphEquiv
      projectiveLineRealizationHomeomorphSphereTwo x
  haveI := subsingleton_homotopyGroup_sphere_of_lt 1 2 (by omega)
    (projectiveLineRealizationHomeomorphSphereTwo x)
  exact ⟨fun a b ↦ e.injective (Subsingleton.elim _ _)⟩

/-- At every basepoint, the second homotopy group of the projective-line realization is `ℤ`. -/
noncomputable def projectiveLinePiTwoMulEquivInt
    (x : SSet.toTop.obj (orderedSSet projectiveLineCycle)) :
    π_ 2 (SSet.toTop.obj (orderedSSet projectiveLineCycle)) x ≃*
      Multiplicative ℤ :=
  (HomotopyGroup.homeomorphMulEquiv
      projectiveLineRealizationHomeomorphSphereTwo x).trans
    (Classical.choice
      (pi2_sphere_two_at_mulEquiv_int
        (projectiveLineRealizationHomeomorphSphereTwo x)))

/-- In every degree, the projective-line realization has the homotopy group of `S²`. -/
noncomputable def projectiveLineHomotopyGroupEquivSphereTwo
    (k : ℕ) (x : SSet.toTop.obj (orderedSSet projectiveLineCycle)) :
    π_ k (SSet.toTop.obj (orderedSSet projectiveLineCycle)) x ≃
      π_ k (SphereSpace 2) (projectiveLineRealizationHomeomorphSphereTwo x) :=
  HomotopyGroup.homeomorphEquiv projectiveLineRealizationHomeomorphSphereTwo x

/-- In every degree, the projective-line realization has the homotopy group of `CP¹`. -/
noncomputable def projectiveLineHomotopyGroupEquivComplexProjectiveLine
    (k : ℕ) (x : SSet.toTop.obj (orderedSSet projectiveLineCycle)) :
    π_ k (SSet.toTop.obj (orderedSSet projectiveLineCycle)) x ≃
      π_ k (ComplexProjectiveModel 1)
        (projectiveLineRealizationHomeomorphComplexProjectiveLine x) :=
  HomotopyGroup.homeomorphEquiv
    projectiveLineRealizationHomeomorphComplexProjectiveLine x

/-- The second homotopy group of the projective-line realization is nontrivial. -/
theorem projectiveLinePiTwo_not_subsingleton
    (x : SSet.toTop.obj (orderedSSet projectiveLineCycle)) :
    ¬ Subsingleton (π_ 2 (SSet.toTop.obj (orderedSSet projectiveLineCycle)) x) := by
  intro h
  have hZ : Subsingleton (Multiplicative ℤ) :=
    projectiveLinePiTwoMulEquivInt x |>.toEquiv.subsingleton_congr.mp h
  have hz := hZ.elim (Multiplicative.ofAdd (0 : ℤ))
    (Multiplicative.ofAdd (1 : ℤ))
  exact Int.zero_ne_one (congrArg Multiplicative.toAdd hz)

/-! ## Restriction of the finite degree-two class -/

/-- Every projective-line triangle is a three-vertex face of the projective-line complex. -/
theorem projectiveLineCycle_faces_self :
    projectiveLineCycle ⊆ facesOfCard projectiveLineCycle 3 := by
  decide

/-- The finite degree-two cochain remains a cocycle on the projective-line subcomplex. -/
theorem projectiveLineDegreeTwoCocycle_isCocycle :
    IsCocycle projectiveLineCycle 2 degreeTwoCocycle := by
  change (facesOfCard projectiveLineCycle 4).filter
      (fun σ ↦ FiniteOrderedComplex.coboundary 3 degreeTwoCocycle σ ≠ 0) = ∅
  decide

/-- The degree-two cochain is not a coboundary on the projective-line subcomplex. -/
theorem projectiveLineDegreeTwoCocycle_not_isCoboundaryOn :
    ¬ IsCoboundaryOn projectiveLineCycle 2 degreeTwoCocycle := by
  apply not_isCoboundaryOn_of_cycle_evaluation_ne_zero
    projectiveLineCycle_faces_self projectiveLineCycle_isCycle
  rw [degreeTwoCocycle_evaluate_projectiveLineCycle]
  decide

/-- The finite degree-two cochain transported to the projective-line simplicial set. -/
def projectiveLineDegreeTwoSSetCochain :
    Submission.Cochain (orderedSSet projectiveLineCycle) (ZMod 2) 2 :=
  toSSetCochain projectiveLineCycle 2 degreeTwoCocycle

/-- The plane's degree-two simplicial cochain pulls back to its projective-line counterpart. -/
theorem degreeTwoSSetCochain_pullback_projectiveLine :
    Cochain.pullback projectiveLineSSetIncl 2 degreeTwoSSetCochain =
      projectiveLineDegreeTwoSSetCochain := by
  ext σ
  rfl

/-- The transported projective-line degree-two cochain is a genuine simplicial cocycle. -/
theorem projectiveLineDegreeTwoSSetCochain_isCocycle :
    Submission.coboundary (orderedSSet projectiveLineCycle) (ZMod 2) 2
        projectiveLineDegreeTwoSSetCochain = 0 := by
  exact toSSetCochain_two_isCocycle degreeTwoCocycle
    projectiveLineDegreeTwoCocycle_isCocycle degreeTwoCocycle_eq_zero_of_card_ne

/-- The restricted cochain bundled as a degree-two simplicial cocycle. -/
def projectiveLineDegreeTwoSSetCocycle :
    cocycles (orderedSSet projectiveLineCycle) (ZMod 2) 2 :=
  ⟨projectiveLineDegreeTwoSSetCochain,
    projectiveLineDegreeTwoSSetCochain_isCocycle⟩

/-- The degree-two simplicial cohomology class on the realized projective line. -/
def projectiveLineDegreeTwoSSetClass :
    Hcoh 2 (orderedSSet projectiveLineCycle) (ZMod 2) :=
  Hcoh.mk projectiveLineDegreeTwoSSetCocycle

/-- Pullback carries the bundled plane cocycle to the bundled projective-line cocycle. -/
theorem degreeTwoSSetCocycle_pullback_projectiveLine :
    cocyclesMap (ZMod 2) projectiveLineSSetIncl 2 degreeTwoSSetCocycle =
      projectiveLineDegreeTwoSSetCocycle := by
  apply Subtype.ext
  exact degreeTwoSSetCochain_pullback_projectiveLine

/-- The projective-line simplicial cochain is not a coboundary. -/
theorem projectiveLineDegreeTwoSSetCochain_not_mem_coboundaries :
    projectiveLineDegreeTwoSSetCochain ∉
      coboundaries (orderedSSet projectiveLineCycle) (ZMod 2) 2 := by
  intro hmem
  change projectiveLineDegreeTwoSSetCochain ∈ LinearMap.range
    (Submission.coboundary (orderedSSet projectiveLineCycle) (ZMod 2) 1) at hmem
  rcases hmem with ⟨b, hb⟩
  apply projectiveLineDegreeTwoCocycle_not_isCoboundaryOn
  apply isCoboundaryOn_of_eq_sSet_coboundary degreeTwoCocycle
    projectiveLineDegreeTwoSSetCochain b hb.symm
  intro σ hσ
  exact toSSetCochain_canonicalSimplex degreeTwoCocycle σ
    (card_eq_of_mem_facesOfCard hσ) (isFace_of_mem_facesOfCard hσ)

/-- The restricted degree-two class is nonzero in genuine simplicial cohomology. -/
theorem projectiveLineDegreeTwoSSetClass_ne_zero :
    projectiveLineDegreeTwoSSetClass ≠ 0 := by
  intro hzero
  apply projectiveLineDegreeTwoSSetCochain_not_mem_coboundaries
  exact (Hcoh.mk_eq_zero_iff projectiveLineDegreeTwoSSetCocycle).1 (by
    simpa only [projectiveLineDegreeTwoSSetClass] using hzero)

/-- The explicit plane class restricts exactly to the projective-line class. -/
theorem degreeTwoSSetClass_restrict_projectiveLine :
    Hcoh.map (ZMod 2) projectiveLineSSetIncl 2 degreeTwoSSetClass =
      projectiveLineDegreeTwoSSetClass := by
  rw [degreeTwoSSetClass, Hcoh.map_mk,
    degreeTwoSSetCocycle_pullback_projectiveLine]
  rfl

/-- The explicit plane class restricts nontrivially to the embedded projective line. -/
theorem degreeTwoSSetClass_restrict_projectiveLine_ne_zero :
    Hcoh.map (ZMod 2) projectiveLineSSetIncl 2 degreeTwoSSetClass ≠ 0 := by
  rw [degreeTwoSSetClass_restrict_projectiveLine]
  exact projectiveLineDegreeTwoSSetClass_ne_zero

end Submission.ComplexProjectivePlaneTriangulation
