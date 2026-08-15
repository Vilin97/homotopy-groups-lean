/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfComplementReduction
import Submission.FiniteOrderedComplexCarrierCollapse

/-!
# Collapse of the complementary finite Hopf piece to a fiber circle

The twenty-seven-tetrahedron complementary preimage in the minimal finite Hopf map admits an
explicit sequence of seventy-two elementary simplicial collapses.  Its endpoint is the triangular
circle on `D₀,D₁,D₂`.  The barycentric strong-deformation-retract theorem for elementary
collapses therefore gives a concrete homotopy equivalence from the complementary piece to the
exact metric circle.  The finite quotient sends that endpoint circle to the target vertex `D`.

This result is weaker than the still-pending homeomorphism with `D² × S¹`, but it proves the
correct homotopy type and identifies the retained core with an actual fiber of the finite map.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- An evaluator-friendly explicit presentation of the canonical complementary facet family. -/
def minimalHopfComplementPreimageCollapseFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {5, 6, 9, 16}, {5, 6, 12, 16}, {5, 7, 8, 15},
    {5, 7, 13, 15}, {5, 8, 9, 15}, {5, 9, 14, 15},
    {5, 9, 14, 16}, {5, 11, 12, 16}, {5, 11, 13, 16},
    {5, 13, 14, 15}, {5, 13, 14, 16}, {6, 7, 9, 16},
    {6, 7, 12, 16}, {7, 8, 10, 16}, {7, 8, 15, 16},
    {7, 9, 10, 16}, {7, 12, 13, 15}, {7, 12, 15, 16},
    {8, 9, 12, 15}, {8, 10, 13, 16}, {8, 11, 12, 16},
    {8, 11, 13, 16}, {8, 12, 15, 16}, {9, 10, 13, 16},
    {9, 12, 13, 15}, {9, 13, 14, 15}, {9, 13, 14, 16} }

theorem minimalHopfComplementPreimageCollapseFacets_eq :
    minimalHopfComplementPreimageCollapseFacets =
      minimalHopfComplementPreimageFacets := by
  decide

/-- Seventy-two elementary collapses from the complementary preimage to its `D`-fiber circle. -/
def minimalHopfComplementCollapseMoves :
    List (ElementaryCollapseMoveData MinimalHopfBallVertex) :=
  [ ⟨{7, 9, 10}, 16⟩,
    ⟨{7, 9, 16}, 6⟩,
    ⟨{6, 7, 12}, 16⟩,
    ⟨{5, 6, 9}, 16⟩,
    ⟨{7, 10, 16}, 8⟩,
    ⟨{5, 6, 16}, 12⟩,
    ⟨{9, 10, 13}, 16⟩,
    ⟨{10, 13, 16}, 8⟩,
    ⟨{5, 9, 16}, 14⟩,
    ⟨{9, 14, 16}, 13⟩,
    ⟨{13, 14, 16}, 5⟩,
    ⟨{5, 13, 14}, 15⟩,
    ⟨{9, 13, 14}, 15⟩,
    ⟨{5, 14, 15}, 9⟩,
    ⟨{5, 13, 16}, 11⟩,
    ⟨{5, 11, 12}, 16⟩,
    ⟨{11, 13, 16}, 8⟩,
    ⟨{9, 13, 15}, 12⟩,
    ⟨{8, 11, 16}, 12⟩,
    ⟨{5, 7, 13}, 15⟩,
    ⟨{12, 13, 15}, 7⟩,
    ⟨{7, 12, 16}, 15⟩,
    ⟨{7, 15, 16}, 8⟩,
    ⟨{8, 15, 16}, 12⟩,
    ⟨{7, 8, 15}, 5⟩,
    ⟨{9, 12, 15}, 8⟩,
    ⟨{5, 9, 15}, 8⟩,
    ⟨{13, 14}, 15⟩,
    ⟨{10, 13}, 8⟩,
    ⟨{7, 10}, 8⟩,
    ⟨{8, 10}, 16⟩,
    ⟨{10, 16}, 9⟩,
    ⟨{7, 9}, 6⟩,
    ⟨{6, 9}, 16⟩,
    ⟨{6, 7}, 16⟩,
    ⟨{7, 16}, 8⟩,
    ⟨{9, 16}, 13⟩,
    ⟨{13, 16}, 8⟩,
    ⟨{6, 16}, 12⟩,
    ⟨{8, 16}, 12⟩,
    ⟨{6, 12}, 5⟩,
    ⟨{5, 12}, 16⟩,
    ⟨{8, 13}, 11⟩,
    ⟨{7, 8}, 5⟩,
    ⟨{8, 11}, 12⟩,
    ⟨{11, 12}, 16⟩,
    ⟨{12, 16}, 15⟩,
    ⟨{11, 16}, 5⟩,
    ⟨{11, 13}, 5⟩,
    ⟨{5, 16}, 14⟩,
    ⟨{5, 13}, 15⟩,
    ⟨{5, 7}, 15⟩,
    ⟨{5, 15}, 8⟩,
    ⟨{13, 15}, 7⟩,
    ⟨{7, 15}, 12⟩,
    ⟨{12, 15}, 8⟩,
    ⟨{7, 12}, 13⟩,
    ⟨{9, 13}, 12⟩,
    ⟨{8, 12}, 9⟩,
    ⟨{10}, 9⟩,
    ⟨{8, 15}, 9⟩,
    ⟨{9, 15}, 14⟩,
    ⟨{9, 14}, 5⟩,
    ⟨{5, 9}, 8⟩,
    ⟨{6}, 5⟩,
    ⟨{11}, 5⟩,
    ⟨{7}, 13⟩,
    ⟨{13}, 12⟩,
    ⟨{12}, 9⟩,
    ⟨{9}, 8⟩,
    ⟨{8}, 5⟩,
    ⟨{5}, 14⟩ ]

/-! The long executable certificate is checked in six chunks. -/

def minimalHopfComplementCollapseChunkZero :=
  minimalHopfComplementCollapseMoves.take 12

def minimalHopfComplementCollapseChunkOne :=
  (minimalHopfComplementCollapseMoves.drop 12).take 12

def minimalHopfComplementCollapseChunkTwo :=
  (minimalHopfComplementCollapseMoves.drop 24).take 12

def minimalHopfComplementCollapseChunkThree :=
  (minimalHopfComplementCollapseMoves.drop 36).take 12

def minimalHopfComplementCollapseChunkFour :=
  (minimalHopfComplementCollapseMoves.drop 48).take 12

def minimalHopfComplementCollapseChunkFive :=
  minimalHopfComplementCollapseMoves.drop 60

theorem minimalHopfComplementCollapseMoves_chunks :
    minimalHopfComplementCollapseMoves =
      minimalHopfComplementCollapseChunkZero ++
      (minimalHopfComplementCollapseChunkOne ++
      (minimalHopfComplementCollapseChunkTwo ++
      (minimalHopfComplementCollapseChunkThree ++
      (minimalHopfComplementCollapseChunkFour ++
        minimalHopfComplementCollapseChunkFive)))) := by
  decide

def minimalHopfComplementCollapseStageTwelveFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {5, 6, 12}, {5, 9, 14}, {5, 12, 16}, {5, 13, 15},
    {5, 13, 16}, {5, 14, 15}, {5, 14, 16}, {6, 7, 9},
    {6, 7, 16}, {6, 9, 16}, {6, 12, 16}, {7, 8, 10},
    {7, 8, 16}, {7, 12, 16}, {8, 10, 13}, {8, 10, 16},
    {8, 13, 16}, {9, 10, 16}, {9, 13, 14}, {9, 13, 16},
    {13, 14, 15}, {5, 7, 8, 15}, {5, 7, 13, 15},
    {5, 8, 9, 15}, {5, 9, 14, 15}, {5, 11, 12, 16},
    {5, 11, 13, 16}, {7, 8, 15, 16}, {7, 12, 13, 15},
    {7, 12, 15, 16}, {8, 9, 12, 15}, {8, 11, 12, 16},
    {8, 11, 13, 16}, {8, 12, 15, 16}, {9, 12, 13, 15},
    {9, 13, 14, 15} }

def minimalHopfComplementCollapseStageTwentyFourFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {5, 6, 12}, {5, 7, 15}, {5, 9, 14}, {5, 9, 15},
    {5, 11, 13}, {5, 11, 16}, {5, 12, 16}, {5, 13, 15},
    {5, 14, 16}, {6, 7, 9}, {6, 7, 16}, {6, 9, 16},
    {6, 12, 16}, {7, 8, 10}, {7, 8, 15}, {7, 8, 16},
    {7, 12, 13}, {7, 12, 15}, {7, 13, 15}, {8, 10, 13},
    {8, 10, 16}, {8, 11, 12}, {8, 11, 13}, {8, 12, 15},
    {8, 12, 16}, {8, 13, 16}, {9, 10, 16}, {9, 12, 13},
    {9, 12, 15}, {9, 13, 16}, {9, 14, 15}, {11, 12, 16},
    {12, 15, 16}, {13, 14, 15}, {5, 7, 8, 15},
    {5, 8, 9, 15}, {8, 9, 12, 15} }

def minimalHopfComplementCollapseStageThirtySixFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {6, 16}, {7, 8}, {8, 13}, {8, 16}, {9, 10}, {9, 16},
    {13, 15}, {14, 15}, {5, 6, 12}, {5, 7, 8}, {5, 7, 15},
    {5, 8, 9}, {5, 8, 15}, {5, 9, 14}, {5, 11, 13},
    {5, 11, 16}, {5, 12, 16}, {5, 13, 15}, {5, 14, 16},
    {6, 12, 16}, {7, 12, 13}, {7, 12, 15}, {7, 13, 15},
    {8, 9, 12}, {8, 9, 15}, {8, 11, 12}, {8, 11, 13},
    {8, 12, 15}, {8, 12, 16}, {8, 13, 16}, {9, 12, 13},
    {9, 13, 16}, {9, 14, 15}, {11, 12, 16}, {12, 15, 16} }

def minimalHopfComplementCollapseStageFortyEightFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {5, 6}, {5, 7}, {5, 8}, {5, 11}, {5, 16}, {8, 12},
    {9, 10}, {9, 13}, {11, 13}, {12, 15}, {13, 15}, {14, 15},
    {15, 16}, {5, 7, 15}, {5, 8, 9}, {5, 8, 15}, {5, 9, 14},
    {5, 11, 13}, {5, 13, 15}, {5, 14, 16}, {7, 12, 13},
    {7, 12, 15}, {7, 13, 15}, {8, 9, 12}, {8, 9, 15},
    {8, 12, 15}, {9, 12, 13}, {9, 14, 15} }

def minimalHopfComplementCollapseStageSixtyFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {9}, {5, 6}, {5, 8}, {5, 11}, {5, 14}, {7, 13},
    {8, 9}, {8, 15}, {9, 12}, {12, 13}, {14, 15}, {14, 16},
    {15, 16}, {5, 8, 9}, {5, 9, 14}, {8, 9, 15},
    {9, 14, 15} }

theorem minimalHopfComplementCollapseChunkZero_valid :
    IsValidElementaryCollapseMoveSequence minimalHopfComplementPreimageCollapseFacets
      minimalHopfComplementCollapseChunkZero := by
  decide

theorem minimalHopfComplementCollapseChunkZero_result :
    applyElementaryCollapseMoves minimalHopfComplementPreimageCollapseFacets
        minimalHopfComplementCollapseChunkZero =
      minimalHopfComplementCollapseStageTwelveFacets := by
  decide

theorem minimalHopfComplementCollapseChunkOne_valid :
    IsValidElementaryCollapseMoveSequence
      minimalHopfComplementCollapseStageTwelveFacets
      minimalHopfComplementCollapseChunkOne := by
  decide

theorem minimalHopfComplementCollapseChunkOne_result :
    applyElementaryCollapseMoves minimalHopfComplementCollapseStageTwelveFacets
        minimalHopfComplementCollapseChunkOne =
      minimalHopfComplementCollapseStageTwentyFourFacets := by
  decide

theorem minimalHopfComplementCollapseChunkTwo_valid :
    IsValidElementaryCollapseMoveSequence
      minimalHopfComplementCollapseStageTwentyFourFacets
      minimalHopfComplementCollapseChunkTwo := by
  decide

theorem minimalHopfComplementCollapseChunkTwo_result :
    applyElementaryCollapseMoves minimalHopfComplementCollapseStageTwentyFourFacets
        minimalHopfComplementCollapseChunkTwo =
      minimalHopfComplementCollapseStageThirtySixFacets := by
  decide

theorem minimalHopfComplementCollapseChunkThree_valid :
    IsValidElementaryCollapseMoveSequence
      minimalHopfComplementCollapseStageThirtySixFacets
      minimalHopfComplementCollapseChunkThree := by
  decide

theorem minimalHopfComplementCollapseChunkThree_result :
    applyElementaryCollapseMoves minimalHopfComplementCollapseStageThirtySixFacets
        minimalHopfComplementCollapseChunkThree =
      minimalHopfComplementCollapseStageFortyEightFacets := by
  decide

theorem minimalHopfComplementCollapseChunkFour_valid :
    IsValidElementaryCollapseMoveSequence
      minimalHopfComplementCollapseStageFortyEightFacets
      minimalHopfComplementCollapseChunkFour := by
  decide

theorem minimalHopfComplementCollapseChunkFour_result :
    applyElementaryCollapseMoves minimalHopfComplementCollapseStageFortyEightFacets
        minimalHopfComplementCollapseChunkFour =
      minimalHopfComplementCollapseStageSixtyFacets := by
  decide

theorem minimalHopfComplementCollapseChunkFive_valid :
    IsValidElementaryCollapseMoveSequence
      minimalHopfComplementCollapseStageSixtyFacets
      minimalHopfComplementCollapseChunkFive := by
  decide

theorem minimalHopfComplementCollapseChunkFive_result :
    applyElementaryCollapseMoves minimalHopfComplementCollapseStageSixtyFacets
        minimalHopfComplementCollapseChunkFive =
      ({{14}, {14, 15}, {14, 16}, {15, 16}} :
        Finset (Finset MinimalHopfBallVertex)) := by
  decide

theorem minimalHopfComplementCollapseMoves_valid :
    IsValidElementaryCollapseMoveSequence
      minimalHopfComplementPreimageFacets
      minimalHopfComplementCollapseMoves := by
  rw [← minimalHopfComplementPreimageCollapseFacets_eq]
  rw [minimalHopfComplementCollapseMoves_chunks,
    isValidElementaryCollapseMoveSequence_append_iff]
  refine ⟨minimalHopfComplementCollapseChunkZero_valid, ?_⟩
  rw [minimalHopfComplementCollapseChunkZero_result,
    isValidElementaryCollapseMoveSequence_append_iff]
  refine ⟨minimalHopfComplementCollapseChunkOne_valid, ?_⟩
  rw [minimalHopfComplementCollapseChunkOne_result,
    isValidElementaryCollapseMoveSequence_append_iff]
  refine ⟨minimalHopfComplementCollapseChunkTwo_valid, ?_⟩
  rw [minimalHopfComplementCollapseChunkTwo_result,
    isValidElementaryCollapseMoveSequence_append_iff]
  refine ⟨minimalHopfComplementCollapseChunkThree_valid, ?_⟩
  rw [minimalHopfComplementCollapseChunkThree_result,
    isValidElementaryCollapseMoveSequence_append_iff]
  exact ⟨minimalHopfComplementCollapseChunkFour_valid, by
    rw [minimalHopfComplementCollapseChunkFour_result]
    exact minimalHopfComplementCollapseChunkFive_valid⟩

/-- The maximal triangular presentation of the retained `D₀D₁D₂` fiber circle. -/
def minimalHopfComplementFiberFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  {{14, 15}, {14, 16}, {15, 16}}

/-- The raw collapse endpoint also contains one redundant vertex facet. -/
def minimalHopfComplementFiberPresentation :
    Finset (Finset MinimalHopfBallVertex) :=
  {{14}, {14, 15}, {14, 16}, {15, 16}}

theorem minimalHopfComplementCollapseMoves_result :
    applyElementaryCollapseMoves minimalHopfComplementPreimageFacets
        minimalHopfComplementCollapseMoves =
      minimalHopfComplementFiberPresentation := by
  rw [← minimalHopfComplementPreimageCollapseFacets_eq]
  rw [minimalHopfComplementCollapseMoves_chunks,
    applyElementaryCollapseMoves_append,
    minimalHopfComplementCollapseChunkZero_result,
    applyElementaryCollapseMoves_append,
    minimalHopfComplementCollapseChunkOne_result,
    applyElementaryCollapseMoves_append,
    minimalHopfComplementCollapseChunkTwo_result,
    applyElementaryCollapseMoves_append,
    minimalHopfComplementCollapseChunkThree_result,
    applyElementaryCollapseMoves_append,
    minimalHopfComplementCollapseChunkFour_result,
    minimalHopfComplementCollapseChunkFive_result]
  rfl

theorem minimalHopfComplementFiberPresentation_le_facets :
    FacetFamilyLE minimalHopfComplementFiberPresentation
      minimalHopfComplementFiberFacets := by
  simp [FacetFamilyLE, IsFace, minimalHopfComplementFiberPresentation,
    minimalHopfComplementFiberFacets]

theorem minimalHopfComplementFiberFacets_le_presentation :
    FacetFamilyLE minimalHopfComplementFiberFacets
      minimalHopfComplementFiberPresentation := by
  simp [FacetFamilyLE, IsFace, minimalHopfComplementFiberPresentation,
    minimalHopfComplementFiberFacets]

theorem minimalHopfComplementFiberPresentation_carrier_eq :
    facetFamilyCarrier minimalHopfComplementFiberPresentation =
      facetFamilyCarrier minimalHopfComplementFiberFacets := by
  apply Set.Subset.antisymm
  · intro x hx
    exact (facetFamilyCarrierMapOfFacetFamilyLE
      minimalHopfComplementFiberPresentation_le_facets ⟨x, hx⟩).2
  · intro x hx
    exact (facetFamilyCarrierMapOfFacetFamilyLE
      minimalHopfComplementFiberFacets_le_presentation ⟨x, hx⟩).2

theorem minimalHopfComplementCollapseResult_carrier_eq :
    facetFamilyCarrier
        (applyElementaryCollapseMoves minimalHopfComplementPreimageFacets
          minimalHopfComplementCollapseMoves) =
      facetFamilyCarrier minimalHopfComplementFiberFacets := by
  rw [minimalHopfComplementCollapseMoves_result]
  exact minimalHopfComplementFiberPresentation_carrier_eq

/-- The complementary affine carrier strongly deformation retracts, through the collapse
sequence, to the retained triangular fiber. -/
noncomputable def minimalHopfComplementCarrierHomotopyEquivFiber :
    ContinuousMap.HomotopyEquiv
      (facetFamilyCarrier minimalHopfComplementPreimageFacets)
      (facetFamilyCarrier minimalHopfComplementFiberFacets) :=
  (elementaryCollapseMoveSequenceCarrierHomotopyEquiv
      minimalHopfComplementPreimageFacets
      minimalHopfComplementCollapseMoves
      minimalHopfComplementCollapseMoves_valid).trans
    (Homeomorph.setCongr
      minimalHopfComplementCollapseResult_carrier_eq).toHomotopyEquiv

/-- The retained triangle is exactly the simplicial boundary on the three `D` vertices. -/
def minimalHopfComplementFiberVertices :
    Finset MinimalHopfBallVertex :=
  {14, 15, 16}

theorem minimalHopfComplementFiberFacets_eq_simplexBoundary :
    minimalHopfComplementFiberFacets =
      simplexBoundaryFacets minimalHopfComplementFiberVertices := by
  decide

theorem minimalHopfComplementFiberVertices_card :
    minimalHopfComplementFiberVertices.card = 2 + 1 := by
  decide

noncomputable def minimalHopfComplementFiberSSetIsoBoundaryTwo :
    orderedSSet minimalHopfComplementFiberFacets ≅
      (SSet.boundary 2 : SSet) :=
  SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex
        minimalHopfComplementFiberFacets_eq_simplexBoundary) ≪≫
    simplexBoundarySSetIso 2 minimalHopfComplementFiberVertices
      minimalHopfComplementFiberVertices_card

noncomputable def minimalHopfComplementFiberRealizationHomeomorphSphereOne :
    SSet.toTop.obj (orderedSSet minimalHopfComplementFiberFacets) ≃ₜ
      SphereSpace 1 :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso
        minimalHopfComplementFiberSSetIsoBoundaryTwo)).trans
    (boundaryRealizationHomeomorphSphere 1)

noncomputable def minimalHopfComplementFiberCarrierHomeomorphSphereOne :
    facetFamilyCarrier minimalHopfComplementFiberFacets ≃ₜ
      SphereSpace 1 :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfComplementFiberFacets).symm.trans
    minimalHopfComplementFiberRealizationHomeomorphSphereOne

/-- The complementary finite Hopf piece has the homotopy type of the exact metric circle. -/
noncomputable def minimalHopfComplementRealizationHomotopyEquivSphereOne :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (orderedSSet minimalHopfComplementPreimageFacets))
      (SphereSpace 1) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfComplementPreimageFacets).toHomotopyEquiv.trans
    (minimalHopfComplementCarrierHomotopyEquivFiber.trans
      minimalHopfComplementFiberCarrierHomeomorphSphereOne.toHomotopyEquiv)

/-- The retained circle is collapsed by the finite Hopf quotient to the target vertex `D`. -/
theorem minimalHopfComplementFiber_quotient_facets :
    minimalHopfComplementFiberFacets.image
        (fun facet ↦ facet.image minimalHopfQuotientVertex) =
      {{8}} := by
  decide

end Submission.ComplexProjectivePlaneTriangulation
