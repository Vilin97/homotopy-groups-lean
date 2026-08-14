/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionInterfaceSolidTorus
import Submission.FiniteOrderedComplexCarrierCollapse
import Submission.SSetBoundaryRealization
import Submission.Lean4TwentyResults

/-!
# Homotopy groups of the projective-plane trisection interfaces

An explicit sequence of twenty-five elementary collapses reduces the standard seven-tetrahedron
solid-torus model to a triangular circle. The general carrier-collapse theorem turns this finite
certificate into a homotopy equivalence with the exact metric circle. Transport across the
pairwise-interface homeomorphisms then computes every positive homotopy group of every pairwise
trisection interface: its fundamental group is infinite cyclic and all higher groups vanish.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped Topology Topology.Homotopy

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def standardSevenVertexSolidTorusCollapseMoves :
    List (ElementaryCollapseMoveData (Fin 7)) :=
  [ ⟨{3, 5, 6}, 1⟩,
    ⟨{3, 4, 6}, 1⟩,
    ⟨{1, 4, 6}, 2⟩,
    ⟨{2, 4, 6}, 0⟩,
    ⟨{2, 4, 5}, 0⟩,
    ⟨{2, 3, 5}, 0⟩,
    ⟨{1, 3, 5}, 0⟩,
    ⟨{5, 6}, 1⟩,
    ⟨{3, 6}, 1⟩,
    ⟨{3, 4}, 1⟩,
    ⟨{1, 6}, 2⟩,
    ⟨{1, 4}, 2⟩,
    ⟨{4, 6}, 0⟩,
    ⟨{4, 5}, 0⟩,
    ⟨{3, 5}, 0⟩,
    ⟨{2, 6}, 0⟩,
    ⟨{2, 5}, 0⟩,
    ⟨{2, 4}, 0⟩,
    ⟨{2, 3}, 0⟩,
    ⟨{1, 5}, 0⟩,
    ⟨{1, 3}, 0⟩,
    ⟨{6}, 0⟩,
    ⟨{5}, 0⟩,
    ⟨{4}, 0⟩,
    ⟨{3}, 0⟩ ]

theorem standardSevenVertexSolidTorusCollapseMoves_valid :
    IsValidElementaryCollapseMoveSequence
      standardSevenVertexSolidTorusFacets
      standardSevenVertexSolidTorusCollapseMoves := by decide

def standardTriangleBoundaryFacets : Finset (Finset (Fin 7)) :=
  {{0, 1}, {0, 2}, {1, 2}}

def standardTriangleBoundaryPresentation : Finset (Finset (Fin 7)) :=
  {{0}, {0, 1}, {0, 2}, {1, 2}}

theorem standardSevenVertexSolidTorusCollapseResult :
    applyElementaryCollapseMoves standardSevenVertexSolidTorusFacets
      standardSevenVertexSolidTorusCollapseMoves =
      standardTriangleBoundaryPresentation := by decide

theorem standardTriangleBoundaryPresentation_le_facets :
    FacetFamilyLE standardTriangleBoundaryPresentation
      standardTriangleBoundaryFacets := by
  unfold FacetFamilyLE IsFace
  decide

theorem standardTriangleBoundaryFacets_le_presentation :
    FacetFamilyLE standardTriangleBoundaryFacets
      standardTriangleBoundaryPresentation := by
  unfold FacetFamilyLE IsFace
  decide

theorem standardTriangleBoundaryPresentation_carrier_eq :
    facetFamilyCarrier standardTriangleBoundaryPresentation =
      facetFamilyCarrier standardTriangleBoundaryFacets := by
  apply Set.Subset.antisymm
  · intro x hx
    exact (facetFamilyCarrierMapOfFacetFamilyLE
      standardTriangleBoundaryPresentation_le_facets ⟨x, hx⟩).2
  · intro x hx
    exact (facetFamilyCarrierMapOfFacetFamilyLE
      standardTriangleBoundaryFacets_le_presentation ⟨x, hx⟩).2

theorem standardSevenVertexSolidTorusCollapseResult_carrier_eq :
    facetFamilyCarrier
        (applyElementaryCollapseMoves standardSevenVertexSolidTorusFacets
          standardSevenVertexSolidTorusCollapseMoves) =
      facetFamilyCarrier standardTriangleBoundaryFacets := by
  rw [standardSevenVertexSolidTorusCollapseResult]
  exact standardTriangleBoundaryPresentation_carrier_eq

noncomputable def standardSevenVertexSolidTorusCarrierHomotopyEquivTriangleBoundary :
    ContinuousMap.HomotopyEquiv
      (facetFamilyCarrier standardSevenVertexSolidTorusFacets)
      (facetFamilyCarrier standardTriangleBoundaryFacets) :=
  (elementaryCollapseMoveSequenceCarrierHomotopyEquiv
      standardSevenVertexSolidTorusFacets
      standardSevenVertexSolidTorusCollapseMoves
      standardSevenVertexSolidTorusCollapseMoves_valid).trans
    (Homeomorph.setCongr
      standardSevenVertexSolidTorusCollapseResult_carrier_eq).toHomotopyEquiv

def standardTriangleVertices : Finset (Fin 7) := {0, 1, 2}

theorem standardTriangleBoundaryFacets_eq_simplexBoundary :
    standardTriangleBoundaryFacets =
      simplexBoundaryFacets standardTriangleVertices := by decide

theorem standardTriangleVertices_card :
    standardTriangleVertices.card = 2 + 1 := by decide

noncomputable def standardTriangleBoundarySSetIsoBoundaryTwo :
    orderedSSet standardTriangleBoundaryFacets ≅
      (SSet.boundary 2 : SSet) :=
  SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex
        standardTriangleBoundaryFacets_eq_simplexBoundary) ≪≫
    simplexBoundarySSetIso 2 standardTriangleVertices
      standardTriangleVertices_card

noncomputable def standardTriangleBoundaryRealizationHomeomorphSphereOne :
    SSet.toTop.obj (orderedSSet standardTriangleBoundaryFacets) ≃ₜ
      SphereSpace 1 :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso standardTriangleBoundarySSetIsoBoundaryTwo)).trans
    (boundaryRealizationHomeomorphSphere 1)

/-- The seven-tetrahedron solid-torus realization deformation-retracts to the exact metric
circle. -/
noncomputable def standardSevenVertexSolidTorusRealizationHomotopyEquivSphereOne :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (orderedSSet standardSevenVertexSolidTorusFacets))
      (SphereSpace 1) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
      standardSevenVertexSolidTorusFacets).toHomotopyEquiv |>.trans
    (standardSevenVertexSolidTorusCarrierHomotopyEquivTriangleBoundary.trans
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        standardTriangleBoundaryFacets).symm.toHomotopyEquiv |>.trans
          standardTriangleBoundaryRealizationHomeomorphSphereOne.toHomotopyEquiv))

/-- Every pairwise trisection interface has the homotopy type of the exact metric circle. -/
noncomputable def pairwiseInterfaceRealizationHomotopyEquivSphereOne
    (a : TrisectionVertex) (ha : a ∈ trisectionApexes)
    (b : TrisectionVertex) (hb : b ∈ trisectionApexes) (hab : a ≠ b) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets a b)))
      (SphereSpace 1) :=
  (pairwiseInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus
      a ha b hb hab).toHomotopyEquiv.trans
    standardSevenVertexSolidTorusRealizationHomotopyEquivSphereOne

/-- The fundamental group of every pairwise trisection interface is infinite cyclic, at every
basepoint. -/
theorem pairwiseInterface_piOne_mulEquiv_int
    (a : TrisectionVertex) (ha : a ∈ trisectionApexes)
    (b : TrisectionVertex) (hb : b ∈ trisectionApexes) (hab : a ≠ b)
    (x : SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets a b))) :
    Nonempty
      (HomotopyGroup.Pi 1
          (SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets a b))) x ≃*
        Multiplicative ℤ) := by
  let e := pairwiseInterfaceRealizationHomotopyEquivSphereOne
    a ha b hb hab
  obtain ⟨changeSpace⟩ := nonempty_mulEquiv_of_homotopyEquiv'
    (N := Fin 1) e x
  obtain ⟨circle⟩ := pi1_sphere_one_mulEquiv_int_at (e x)
  exact ⟨changeSpace.trans circle⟩

/-- Every homotopy group above degree one of a pairwise trisection interface vanishes, at every
basepoint. -/
theorem pairwiseInterface_higher_homotopy_subsingleton
    (a : TrisectionVertex) (ha : a ∈ trisectionApexes)
    (b : TrisectionVertex) (hb : b ∈ trisectionApexes) (hab : a ≠ b)
    (k : ℕ)
    (x : SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets a b))) :
    Subsingleton
      (HomotopyGroup.Pi (k + 2)
        (SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets a b))) x) := by
  let e := pairwiseInterfaceRealizationHomotopyEquivSphereOne
    a ha b hb hab
  letI : Subsingleton
      (HomotopyGroup.Pi (k + 2) (SphereSpace 1) (e x)) :=
    sphere_one_higher_homotopy_subsingleton_at k (e x)
  obtain ⟨changeSpace⟩ := nonempty_mulEquiv_of_homotopyEquiv'
    (N := Fin (k + 2)) e x
  exact changeSpace.injective.subsingleton

end Submission.ComplexProjectivePlaneTriangulation
