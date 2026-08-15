/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTriangulation
import Submission.BistellarSphereRealization
import Submission.Cohomology.FiniteOrderedComplexMap
import Submission.Cohomology.FiniteOrderedComplexReindex
import Submission.FiniteOrderedComplexCarrierFunctorial
import Submission.SSetBoundaryRealization

/-!
# The finite Hopf quotient behind the nine-vertex projective plane

Madahar--Sarkaria construct their nine-vertex projective-plane triangulation from a
twelve-vertex simplicial model of the Hopf map and a seventeen-vertex triangulated four-ball.
This file records the finite data from that construction in the vertex convention

`1,2,3,4,5,A₀,A₁,A₂,B₀,B₁,B₂,C₀,C₁,C₂,D₀,D₁,D₂`.

The thirty-two displayed four-simplices generate eighty-eight facets under the order-three
symmetry `(123)(Aᵢ Bᵢ₊₁ Cᵢ₊₂)`.  Their incidence-one boundary is exactly the displayed
thirty-six-tetrahedron complex.  Collapsing each indexed triple `Aᵢ`, `Bᵢ`, `Cᵢ`, and `Dᵢ`
gives a monotone vertex map to `1,2,3,4,5,A,B,C,D`.  On the boundary its four facet images are
the boundary of the tetrahedron `ABCD`; on the four-dimensional complex its thirty-six
nondegenerate top images are exactly the maintained nine-vertex projective-plane facets.

The quotient data is packaged as a commuting square of genuine simplicial maps and, after
realization, continuous maps.  This is the finite combinatorial input for the remaining
topological comparison with the concrete Hopf map and geometric `CP²`.

The results below certify the boundary as an exact three-sphere and the target as an exact
two-sphere.  They do not yet identify the realized sphere map with the quadratic Hopf map, nor
do they yet prove that the realization of the full seventeen-vertex complex is a four-ball.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Vertices of the four-ball construction, ordered as
`1,2,3,4,5,A₀,A₁,A₂,B₀,B₁,B₂,C₀,C₁,C₂,D₀,D₁,D₂`. -/
abbrev MinimalHopfBallVertex := Fin 17

/-- The order-three symmetry used to generate the unlisted facets. -/
def minimalHopfBallRotation : MinimalHopfBallVertex → MinimalHopfBallVertex :=
  ![1, 2, 0, 3, 4, 9, 10, 8, 12, 13, 11, 6, 7, 5, 14, 15, 16]

/-- The displayed symmetry has order three on every vertex. -/
theorem minimalHopfBallRotation_order_three (v : MinimalHopfBallVertex) :
    minimalHopfBallRotation
        (minimalHopfBallRotation (minimalHopfBallRotation v)) = v := by
  fin_cases v <;> decide

/-- Apply the threefold symmetry to one facet. -/
def rotateMinimalHopfFacet (facet : Finset MinimalHopfBallVertex) :
    Finset MinimalHopfBallVertex :=
  facet.image minimalHopfBallRotation

/-- Close a displayed facet family under the order-three symmetry. -/
def minimalHopfThreefoldOrbit
    (displayed : Finset (Finset MinimalHopfBallVertex)) :
    Finset (Finset MinimalHopfBallVertex) :=
  displayed ∪ displayed.image rotateMinimalHopfFacet ∪
    (displayed.image rotateMinimalHopfFacet).image rotateMinimalHopfFacet

/-- The thirty-two displayed representatives of the seventeen-vertex four-dimensional
complex. -/
def minimalHopfBallDisplayedFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {0, 5, 8, 9, 12}, {0, 5, 11, 12, 16}, {0, 2, 5, 8, 11},
    {0, 3, 5, 8, 9}, {1, 2, 3, 7, 15}, {0, 2, 3, 4, 5},
    {0, 5, 8, 11, 12}, {0, 8, 12, 15, 16}, {0, 2, 8, 15, 16},
    {0, 4, 5, 6, 9}, {0, 1, 2, 15, 16}, {0, 1, 2, 3, 15},
    {0, 5, 6, 9, 12}, {3, 5, 8, 9, 15}, {1, 2, 7, 10, 16},
    {0, 4, 5, 6, 16}, {0, 1, 4, 6, 9}, {0, 1, 2, 4, 16},
    {0, 8, 9, 12, 15}, {3, 5, 9, 14, 15}, {1, 4, 6, 9, 16},
    {2, 3, 5, 7, 15}, {0, 2, 3, 5, 8}, {0, 1, 2, 3, 4},
    {0, 8, 11, 12, 16}, {4, 5, 9, 14, 16}, {3, 4, 5, 9, 14},
    {0, 3, 4, 5, 9}, {0, 5, 6, 12, 16}, {4, 5, 6, 9, 16},
    {2, 3, 5, 8, 15}, {0, 1, 4, 6, 16} }

/-- All eighty-eight four-simplices of the seventeen-vertex construction. -/
def minimalHopfBallFacets : Finset (Finset MinimalHopfBallVertex) :=
  minimalHopfThreefoldOrbit minimalHopfBallDisplayedFacets

/-- The symmetry closure contains exactly eighty-eight four-simplices. -/
theorem minimalHopfBallFacets_card : minimalHopfBallFacets.card = 88 := by
  decide

/-- Every facet of the seventeen-vertex complex is four-dimensional. -/
theorem minimalHopfBallFacets_pure :
    ∀ facet ∈ minimalHopfBallFacets, facet.card = 5 := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfBallFacets, σ.1.card = 5)
    ⟨facet, hfacet⟩

/-- The verified f-vector of the seventeen-vertex complex. -/
theorem minimalHopfBall_f_vector :
    ((facesOfCard minimalHopfBallFacets 1).card,
      (facesOfCard minimalHopfBallFacets 2).card,
      (facesOfCard minimalHopfBallFacets 3).card,
      (facesOfCard minimalHopfBallFacets 4).card,
      (facesOfCard minimalHopfBallFacets 5).card) =
        (17, 98, 232, 238, 88) := by
  decide

/-- Tetrahedra having incidence one in a pure four-dimensional facet family. -/
def fourComplexBoundaryTetrahedra
    (fourFacets : Finset (Finset MinimalHopfBallVertex)) :
    Finset (Finset MinimalHopfBallVertex) :=
  (facesOfCard fourFacets 4).filter fun tetrahedron ↦
    (fourFacets.filter fun facet ↦
      tetrahedron ∈ facet.powersetCard 4).card = 1

/-- Eight representatives whose symmetry orbits give the first three boundary cells. -/
def minimalHopfSphereOrbitRepresentatives :
    Finset (Finset MinimalHopfBallVertex) :=
  { {5, 8, 9, 12}, {5, 8, 11, 12}, {5, 6, 9, 12},
    {8, 9, 12, 15}, {8, 11, 12, 16}, {5, 6, 12, 16},
    {5, 11, 12, 16}, {8, 12, 15, 16} }

/-- The twelve remaining displayed boundary tetrahedra. -/
def minimalHopfSphereExceptionalFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {5, 8, 9, 15}, {5, 9, 14, 15}, {9, 12, 13, 15},
    {9, 13, 14, 15}, {5, 7, 13, 15}, {5, 13, 14, 15},
    {5, 9, 14, 16}, {5, 6, 9, 16}, {9, 13, 14, 16},
    {9, 10, 13, 16}, {5, 13, 14, 16}, {5, 11, 13, 16} }

/-- The thirty-six-tetrahedron boundary complex carrying the finite Hopf map. -/
def minimalHopfSphereFacets : Finset (Finset MinimalHopfBallVertex) :=
  minimalHopfThreefoldOrbit minimalHopfSphereOrbitRepresentatives ∪
    minimalHopfSphereExceptionalFacets

/-- The displayed boundary family has thirty-six tetrahedra. -/
theorem minimalHopfSphereFacets_card : minimalHopfSphereFacets.card = 36 := by
  decide


/-- Every displayed boundary facet is a tetrahedron. -/
theorem minimalHopfSphereFacets_pure :
    ∀ facet ∈ minimalHopfSphereFacets, facet.card = 4 := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfSphereFacets, σ.1.card = 4)
    ⟨facet, hfacet⟩

/-- The incidence-one boundary of the eighty-eight-facet complex is exactly the displayed
thirty-six-tetrahedron complex. -/
theorem minimalHopfBall_boundary :
    fourComplexBoundaryTetrahedra minimalHopfBallFacets =
      minimalHopfSphereFacets := by
  decide

/-- Every tetrahedron of the four-dimensional complex has incidence one or two. -/
theorem minimalHopfBall_tetrahedron_incidence :
    ∀ tetrahedron ∈ facesOfCard minimalHopfBallFacets 4,
      (minimalHopfBallFacets.filter fun facet ↦
        tetrahedron ∈ facet.powersetCard 4).card = 1 ∨
      (minimalHopfBallFacets.filter fun facet ↦
        tetrahedron ∈ facet.powersetCard 4).card = 2 := by
  intro tetrahedron htetrahedron
  exact (by decide : ∀ σ : ↥(facesOfCard minimalHopfBallFacets 4),
    (minimalHopfBallFacets.filter fun facet ↦
      σ.1 ∈ facet.powersetCard 4).card = 1 ∨
    (minimalHopfBallFacets.filter fun facet ↦
      σ.1 ∈ facet.powersetCard 4).card = 2) ⟨tetrahedron, htetrahedron⟩

/-- The boundary has the f-vector of the displayed twelve-vertex three-sphere. -/
theorem minimalHopfSphere_f_vector :
    ((facesOfCard minimalHopfSphereFacets 1).card,
      (facesOfCard minimalHopfSphereFacets 2).card,
      (facesOfCard minimalHopfSphereFacets 3).card,
      (facesOfCard minimalHopfSphereFacets 4).card) =
        (12, 48, 72, 36) := by
  decide

/-- Every boundary triangle belongs to exactly two boundary tetrahedra. -/
theorem minimalHopfSphere_triangle_incidence_two :
    ∀ triangle ∈ facesOfCard minimalHopfSphereFacets 3,
      (minimalHopfSphereFacets.filter fun tetrahedron ↦
        triangle ∈ tetrahedron.powersetCard 3).card = 2 := by
  intro triangle htriangle
  exact (by decide : ∀ σ : ↥(facesOfCard minimalHopfSphereFacets 3),
    (minimalHopfSphereFacets.filter fun tetrahedron ↦
      σ.1 ∈ tetrahedron.powersetCard 3).card = 2) ⟨triangle, htriangle⟩

/-! ## Exact recognition of the domain sphere -/

/-- Seventeen reducing bistellar moves from the thirty-six-tetrahedron domain to a
four-simplex boundary. -/
def minimalHopfSphereBistellarMoves :
    List (BistellarMoveData MinimalHopfBallVertex) :=
  [⟨{5, 6}, {9, 12, 16}⟩,
    ⟨{6}, {7, 9, 12, 16}⟩,
    ⟨{9, 10}, {7, 13, 16}⟩,
    ⟨{10}, {7, 8, 13, 16}⟩,
    ⟨{5, 7}, {8, 13, 15}⟩,
    ⟨{11, 12}, {5, 8, 16}⟩,
    ⟨{11}, {5, 8, 13, 16}⟩,
    ⟨{7, 8}, {13, 15, 16}⟩,
    ⟨{8, 13}, {5, 15, 16}⟩,
    ⟨{5, 12}, {8, 9, 16}⟩,
    ⟨{5, 8}, {9, 15, 16}⟩,
    ⟨{8}, {9, 12, 15, 16}⟩,
    ⟨{5, 9}, {14, 15, 16}⟩,
    ⟨{5}, {13, 14, 15, 16}⟩,
    ⟨{14}, {9, 13, 15, 16}⟩,
    ⟨{7, 9}, {12, 13, 16}⟩,
    ⟨{7}, {12, 13, 15, 16}⟩]

/-- The first four moves in the reduction. -/
def minimalHopfSphereBistellarChunkZero :
    List (BistellarMoveData MinimalHopfBallVertex) :=
  [⟨{5, 6}, {9, 12, 16}⟩,
    ⟨{6}, {7, 9, 12, 16}⟩,
    ⟨{9, 10}, {7, 13, 16}⟩,
    ⟨{10}, {7, 8, 13, 16}⟩]

/-- The next four moves in the reduction. -/
def minimalHopfSphereBistellarChunkOne :
    List (BistellarMoveData MinimalHopfBallVertex) :=
  [⟨{5, 7}, {8, 13, 15}⟩,
    ⟨{11, 12}, {5, 8, 16}⟩,
    ⟨{11}, {5, 8, 13, 16}⟩,
    ⟨{7, 8}, {13, 15, 16}⟩]

/-- The middle four moves in the reduction. -/
def minimalHopfSphereBistellarChunkTwo :
    List (BistellarMoveData MinimalHopfBallVertex) :=
  [⟨{8, 13}, {5, 15, 16}⟩,
    ⟨{5, 12}, {8, 9, 16}⟩,
    ⟨{5, 8}, {9, 15, 16}⟩,
    ⟨{8}, {9, 12, 15, 16}⟩]

/-- The following three moves in the reduction. -/
def minimalHopfSphereBistellarChunkThree :
    List (BistellarMoveData MinimalHopfBallVertex) :=
  [⟨{5, 9}, {14, 15, 16}⟩,
    ⟨{5}, {13, 14, 15, 16}⟩,
    ⟨{14}, {9, 13, 15, 16}⟩]

/-- The final two moves in the reduction. -/
def minimalHopfSphereBistellarChunkFour :
    List (BistellarMoveData MinimalHopfBallVertex) :=
  [⟨{7, 9}, {12, 13, 16}⟩,
    ⟨{7}, {12, 13, 15, 16}⟩]

/-- The five chunks concatenate to the displayed seventeen-move sequence. -/
theorem minimalHopfSphereBistellarMoves_chunks :
    minimalHopfSphereBistellarMoves =
      minimalHopfSphereBistellarChunkZero ++
      (minimalHopfSphereBistellarChunkOne ++
      (minimalHopfSphereBistellarChunkTwo ++
      (minimalHopfSphereBistellarChunkThree ++
        minimalHopfSphereBistellarChunkFour))) := by
  rfl

/-- The explicit facet state after the first four moves. -/
def minimalHopfSphereBistellarStageOneFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {5, 7, 8, 13}, {5, 7, 8, 15}, {5, 7, 13, 15}, {5, 8, 9, 12},
    {5, 8, 9, 15}, {5, 8, 11, 12}, {5, 8, 11, 13}, {5, 9, 12, 16},
    {5, 9, 14, 15}, {5, 9, 14, 16}, {5, 11, 12, 16}, {5, 11, 13, 16},
    {5, 13, 14, 15}, {5, 13, 14, 16}, {7, 8, 13, 16}, {7, 8, 15, 16},
    {7, 9, 12, 13}, {7, 9, 12, 16}, {7, 9, 13, 16}, {7, 12, 13, 15},
    {7, 12, 15, 16}, {8, 9, 12, 15}, {8, 11, 12, 16}, {8, 11, 13, 16},
    {8, 12, 15, 16}, {9, 12, 13, 15}, {9, 13, 14, 15}, {9, 13, 14, 16} }

theorem minimalHopfSphereBistellarChunkZero_valid :
    IsValidBistellarMoveSequence minimalHopfSphereFacets 3
      minimalHopfSphereBistellarChunkZero := by
  decide

theorem minimalHopfSphereBistellarChunkZero_result :
    applyBistellarMoves minimalHopfSphereFacets
        minimalHopfSphereBistellarChunkZero =
      minimalHopfSphereBistellarStageOneFacets := by
  decide

/-- The explicit facet state after the first eight moves. -/
def minimalHopfSphereBistellarStageTwoFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {5, 8, 9, 12}, {5, 8, 9, 15}, {5, 8, 12, 16}, {5, 8, 13, 15},
    {5, 8, 13, 16}, {5, 9, 12, 16}, {5, 9, 14, 15}, {5, 9, 14, 16},
    {5, 13, 14, 15}, {5, 13, 14, 16}, {7, 9, 12, 13}, {7, 9, 12, 16},
    {7, 9, 13, 16}, {7, 12, 13, 15}, {7, 12, 15, 16}, {7, 13, 15, 16},
    {8, 9, 12, 15}, {8, 12, 15, 16}, {8, 13, 15, 16}, {9, 12, 13, 15},
    {9, 13, 14, 15}, {9, 13, 14, 16} }

theorem minimalHopfSphereBistellarChunkOne_valid :
    IsValidBistellarMoveSequence minimalHopfSphereBistellarStageOneFacets 3
      minimalHopfSphereBistellarChunkOne := by
  decide

theorem minimalHopfSphereBistellarChunkOne_result :
    applyBistellarMoves minimalHopfSphereBistellarStageOneFacets
        minimalHopfSphereBistellarChunkOne =
      minimalHopfSphereBistellarStageTwoFacets := by
  decide

/-- The explicit facet state after the first twelve moves. -/
def minimalHopfSphereBistellarStageThreeFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {5, 9, 14, 15}, {5, 9, 14, 16}, {5, 9, 15, 16}, {5, 13, 14, 15},
    {5, 13, 14, 16}, {5, 13, 15, 16}, {7, 9, 12, 13}, {7, 9, 12, 16},
    {7, 9, 13, 16}, {7, 12, 13, 15}, {7, 12, 15, 16}, {7, 13, 15, 16},
    {9, 12, 13, 15}, {9, 12, 15, 16}, {9, 13, 14, 15}, {9, 13, 14, 16} }

theorem minimalHopfSphereBistellarChunkTwo_valid :
    IsValidBistellarMoveSequence minimalHopfSphereBistellarStageTwoFacets 3
      minimalHopfSphereBistellarChunkTwo := by
  decide

theorem minimalHopfSphereBistellarChunkTwo_result :
    applyBistellarMoves minimalHopfSphereBistellarStageTwoFacets
        minimalHopfSphereBistellarChunkTwo =
      minimalHopfSphereBistellarStageThreeFacets := by
  decide

/-- The explicit facet state after the first fifteen moves. -/
def minimalHopfSphereBistellarStageFourFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {7, 9, 12, 13}, {7, 9, 12, 16}, {7, 9, 13, 16}, {7, 12, 13, 15},
    {7, 12, 15, 16}, {7, 13, 15, 16}, {9, 12, 13, 15}, {9, 12, 15, 16},
    {9, 13, 15, 16} }

theorem minimalHopfSphereBistellarChunkThree_valid :
    IsValidBistellarMoveSequence minimalHopfSphereBistellarStageThreeFacets 3
      minimalHopfSphereBistellarChunkThree := by
  decide

theorem minimalHopfSphereBistellarChunkThree_result :
    applyBistellarMoves minimalHopfSphereBistellarStageThreeFacets
        minimalHopfSphereBistellarChunkThree =
      minimalHopfSphereBistellarStageFourFacets := by
  decide

theorem minimalHopfSphereBistellarChunkFour_valid :
    IsValidBistellarMoveSequence minimalHopfSphereBistellarStageFourFacets 3
      minimalHopfSphereBistellarChunkFour := by
  decide

theorem minimalHopfSphereBistellarChunkFour_result :
    applyBistellarMoves minimalHopfSphereBistellarStageFourFacets
        minimalHopfSphereBistellarChunkFour =
      simplexBoundaryFacets {9, 12, 13, 15, 16} := by
  decide

/-- Every move in the displayed reduction is valid at the stage where it is applied. -/
theorem minimalHopfSphereBistellarMoves_valid :
    IsValidBistellarMoveSequence minimalHopfSphereFacets 3
      minimalHopfSphereBistellarMoves := by
  rw [minimalHopfSphereBistellarMoves_chunks,
    isValidBistellarMoveSequence_append_iff]
  refine ⟨minimalHopfSphereBistellarChunkZero_valid, ?_⟩
  rw [minimalHopfSphereBistellarChunkZero_result,
    isValidBistellarMoveSequence_append_iff]
  refine ⟨minimalHopfSphereBistellarChunkOne_valid, ?_⟩
  rw [minimalHopfSphereBistellarChunkOne_result,
    isValidBistellarMoveSequence_append_iff]
  refine ⟨minimalHopfSphereBistellarChunkTwo_valid, ?_⟩
  rw [minimalHopfSphereBistellarChunkTwo_result,
    isValidBistellarMoveSequence_append_iff]
  exact ⟨minimalHopfSphereBistellarChunkThree_valid, by
    rw [minimalHopfSphereBistellarChunkThree_result]
    exact minimalHopfSphereBistellarChunkFour_valid⟩

/-- The reducing sequence ends at exactly the boundary of the displayed four-simplex. -/
theorem minimalHopfSphere_bistellar_result :
    applyBistellarMoves minimalHopfSphereFacets
        minimalHopfSphereBistellarMoves =
      simplexBoundaryFacets {9, 12, 13, 15, 16} := by
  rw [minimalHopfSphereBistellarMoves_chunks,
    applyBistellarMoves_append, minimalHopfSphereBistellarChunkZero_result,
    applyBistellarMoves_append, minimalHopfSphereBistellarChunkOne_result,
    applyBistellarMoves_append, minimalHopfSphereBistellarChunkTwo_result,
    applyBistellarMoves_append, minimalHopfSphereBistellarChunkThree_result,
    minimalHopfSphereBistellarChunkFour_result]

/-- The finite Hopf domain is a certified combinatorial three-sphere. -/
theorem minimalHopfSphere_isBistellarThreeSphere :
    IsBistellarSphere minimalHopfSphereFacets 3 :=
  ⟨minimalHopfSphereBistellarMoves, {9, 12, 13, 15, 16}, by decide,
    minimalHopfSphereBistellarMoves_valid,
    minimalHopfSphere_bistellar_result⟩

/-- The computed endpoint is the standard simplicial four-simplex boundary. -/
noncomputable def minimalHopfSphereBistellarResultSSetIso :
    orderedSSet
        (applyBistellarMoves minimalHopfSphereFacets
          minimalHopfSphereBistellarMoves) ≅
      (SSet.boundary 4 : SSet) :=
  SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex minimalHopfSphere_bistellar_result) ≪≫
    simplexBoundarySSetIso 4 {9, 12, 13, 15, 16} (by decide)

/-- Exact realization isomorphism from the finite Hopf domain to the standard simplicial
three-sphere. -/
noncomputable def minimalHopfDomainRealizationIsoBoundaryFour :
    SSet.toTop.obj (orderedSSet minimalHopfSphereFacets) ≅
      SSet.toTop.obj (SSet.boundary 4 : SSet) :=
  bistellarMoveSequenceRealizationIso minimalHopfSphereFacets 3
      minimalHopfSphereBistellarMoves minimalHopfSphereBistellarMoves_valid ≪≫
    SSet.toTop.mapIso minimalHopfSphereBistellarResultSSetIso

/-- The realization of the twelve-vertex finite Hopf domain is the exact metric
three-sphere. -/
noncomputable def minimalHopfDomainRealizationHomeomorphSphereThree :
    SSet.toTop.obj (orderedSSet minimalHopfSphereFacets) ≃ₜ SphereSpace 3 :=
  (TopCat.homeoOfIso minimalHopfDomainRealizationIsoBoundaryFour).trans
    (boundaryRealizationHomeomorphSphere 3)

/-! ## The finite quotient -/

/-- Collapse the indexed vertex triples to the nine labels
`1,2,3,4,5,A,B,C,D`. -/
def minimalHopfQuotientVertex : MinimalHopfBallVertex →o Vertex where
  toFun := ![0, 1, 2, 3, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 8, 8, 8]
  monotone' := by decide

/-- The four vertices `A,B,C,D` supporting the target tetrahedron boundary. -/
def minimalHopfTargetVertices : Finset Vertex := {5, 6, 7, 8}

/-- The four-triangle target of the finite Hopf map. -/
def minimalHopfTargetFacets : Finset (Finset Vertex) :=
  simplexBoundaryFacets minimalHopfTargetVertices

/-- The target really has four triangles. -/
theorem minimalHopfTargetFacets_card : minimalHopfTargetFacets.card = 4 := by
  decide

/-- Collapsing the boundary facets gives exactly the four target triangles. -/
theorem minimalHopfSphere_quotient_facets :
    minimalHopfSphereFacets.image
        (fun facet ↦ facet.image minimalHopfQuotientVertex) =
      minimalHopfTargetFacets := by
  decide

/-- The nondegenerate four-dimensional images of the seventeen-vertex complex are exactly the
thirty-six maintained projective-plane facets. -/
theorem minimalHopfBall_quotient_top_facets :
    (minimalHopfBallFacets.image
        (fun facet ↦ facet.image minimalHopfQuotientVertex)).filter
          (fun facet ↦ facet.card = 5) = facets := by
  decide

/-- Every four-ball facet maps to a face of the maintained nine-vertex projective-plane
complex. -/
theorem minimalHopfBallFacetFamilyMapsTo :
    FacetFamilyMapsTo minimalHopfQuotientVertex minimalHopfBallFacets facets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfBallFacets,
    IsFace facets (σ.1.image minimalHopfQuotientVertex)) ⟨facet, hfacet⟩

/-- Every boundary tetrahedron maps to a face of the target two-sphere. -/
theorem minimalHopfSphereFacetFamilyMapsTo :
    FacetFamilyMapsTo minimalHopfQuotientVertex
      minimalHopfSphereFacets minimalHopfTargetFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfSphereFacets,
    IsFace minimalHopfTargetFacets
      (σ.1.image minimalHopfQuotientVertex)) ⟨facet, hfacet⟩

/-- The displayed boundary tetrahedra are faces of the four-dimensional complex. -/
theorem minimalHopfSphereFacets_le_ball :
    FacetFamilyLE minimalHopfSphereFacets minimalHopfBallFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfSphereFacets,
    IsFace minimalHopfBallFacets σ.1) ⟨facet, hfacet⟩

/-- The four-triangle Hopf target is an embedded subcomplex of the maintained projective-plane
triangulation. -/
theorem minimalHopfTargetFacets_le_projectivePlane :
    FacetFamilyLE minimalHopfTargetFacets facets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfTargetFacets,
    IsFace facets σ.1) ⟨facet, hfacet⟩

/-- The finite simplicial Hopf-map candidate from the twelve-vertex boundary to the
four-triangle sphere. -/
def minimalHopfSSetMap :
    orderedSSet minimalHopfSphereFacets ⟶
      orderedSSet minimalHopfTargetFacets :=
  orderedSSetMapOfMonotone minimalHopfQuotientVertex
    minimalHopfSphereFacetFamilyMapsTo

/-- The simplicial quotient from the seventeen-vertex complex to the maintained nine-vertex
projective-plane complex. -/
def minimalHopfBallQuotientSSetMap :
    orderedSSet minimalHopfBallFacets ⟶ projectivePlaneSSet :=
  orderedSSetMapOfMonotone minimalHopfQuotientVertex
    minimalHopfBallFacetFamilyMapsTo

/-- Inclusion of the finite Hopf domain into the seventeen-vertex complex. -/
def minimalHopfSphereSSetIncl :
    orderedSSet minimalHopfSphereFacets ⟶
      orderedSSet minimalHopfBallFacets :=
  orderedSSetHomOfFacetFamilyLE minimalHopfSphereFacets_le_ball

/-- Inclusion of the four-triangle Hopf target into the nine-vertex projective-plane complex. -/
def minimalHopfTargetSSetIncl :
    orderedSSet minimalHopfTargetFacets ⟶ projectivePlaneSSet :=
  orderedSSetHomOfFacetFamilyLE minimalHopfTargetFacets_le_projectivePlane

/-- The finite Hopf map and four-dimensional quotient form a strictly commuting simplicial
square. -/
theorem minimalHopfQuotient_sSet_square :
    minimalHopfSphereSSetIncl ≫ minimalHopfBallQuotientSSetMap =
      minimalHopfSSetMap ≫ minimalHopfTargetSSetIncl := by
  ext Δ x
  rfl

/-! ## Realization -/

/-- Realization of the finite Hopf-map candidate. -/
noncomputable def minimalHopfRealizationMap :
    SSet.toTop.obj (orderedSSet minimalHopfSphereFacets) ⟶
      SSet.toTop.obj (orderedSSet minimalHopfTargetFacets) :=
  SSet.toTop.map minimalHopfSSetMap

/-- Realization of the finite four-dimensional quotient. -/
noncomputable def minimalHopfBallQuotientRealizationMap :
    SSet.toTop.obj (orderedSSet minimalHopfBallFacets) ⟶
      projectivePlaneRealization :=
  SSet.toTop.map minimalHopfBallQuotientSSetMap

/-- The realized quotient square commutes strictly. -/
theorem minimalHopfQuotient_realization_square :
    SSet.toTop.map minimalHopfSphereSSetIncl ≫
        minimalHopfBallQuotientRealizationMap =
      minimalHopfRealizationMap ≫
        SSet.toTop.map minimalHopfTargetSSetIncl := by
  rw [minimalHopfBallQuotientRealizationMap, minimalHopfRealizationMap,
    ← SSet.toTop.map_comp, ← SSet.toTop.map_comp,
    minimalHopfQuotient_sSet_square]

/-- The four target vertices have the expected cardinality. -/
theorem minimalHopfTargetVertices_card :
    minimalHopfTargetVertices.card = 3 + 1 := by
  decide

/-- The four-triangle target is the standard simplicial three-simplex boundary. -/
noncomputable def minimalHopfTargetSSetIsoBoundaryThree :
    orderedSSet minimalHopfTargetFacets ≅ (SSet.boundary 3 : SSet) :=
  simplexBoundarySSetIso 3 minimalHopfTargetVertices
    minimalHopfTargetVertices_card

/-- The realization of the finite Hopf target is the exact metric two-sphere. -/
noncomputable def minimalHopfTargetRealizationHomeomorphSphereTwo :
    SSet.toTop.obj (orderedSSet minimalHopfTargetFacets) ≃ₜ SphereSpace 2 :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso minimalHopfTargetSSetIsoBoundaryThree)).trans
    (boundaryRealizationHomeomorphSphere 2)

/-- The finite simplicial map expressed in the maintained exact metric-sphere coordinates.  The
remaining geometric comparison is to identify this concrete sphere map with the quadratic Hopf
map already used elsewhere in the development. -/
noncomputable def minimalHopfSphereCoordinateTopCat :
    TopCat.of (SphereSpace 3) ⟶ TopCat.of (SphereSpace 2) :=
  (TopCat.isoOfHomeo
      minimalHopfDomainRealizationHomeomorphSphereThree).inv ≫
    minimalHopfRealizationMap ≫
      (TopCat.isoOfHomeo
        minimalHopfTargetRealizationHomeomorphSphereTwo).hom

end Submission.ComplexProjectivePlaneTriangulation
