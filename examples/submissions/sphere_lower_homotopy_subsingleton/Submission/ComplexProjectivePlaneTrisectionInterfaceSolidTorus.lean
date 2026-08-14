/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionInterfaceCertificate
import Submission.ComplexProjectivePlaneTrisectionCentralTorus

/-!
# Bistellar reduction of a pairwise interface to the standard solid torus

Lifting the three verified bistellar moves on the spherical base of the ten-tetrahedron ball,
then eliminating its cone apex, gives four valid three-dimensional moves on the whole pairwise
interface. Their exact endpoint is the classical seven-vertex, seven-tetrahedron solid-torus
triangulation. Its incidence boundary is the standard fourteen-triangle torus.

Ordered reindexing, arbitrary affine carrier reindexing, and realization invariance of bistellar
sequences turn this finite reduction into a homeomorphism of geometric realizations.
-/

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def zeroFiveInterfaceBistellarSolidTorusMoves :
    List (BistellarMoveData TrisectionVertex) :=
  zeroFiveInterfaceBallTwoBaseBistellarMoves.map (coneBistellarMoveData 9) ++
    [⟨{9}, {1, 7, 8, 12}⟩]

theorem zeroFiveInterfaceBistellarSolidTorusMoves_valid :
    IsValidBistellarMoveSequence (pairwiseInterfaceFacets 0 5) 3
      zeroFiveInterfaceBistellarSolidTorusMoves := by decide

def zeroFiveInterfaceBistellarSolidTorusResult :
    Finset (Finset TrisectionVertex) :=
  applyBistellarMoves (pairwiseInterfaceFacets 0 5)
    zeroFiveInterfaceBistellarSolidTorusMoves

theorem zeroFiveInterfaceBistellarSolidTorusResult_eq :
    zeroFiveInterfaceBistellarSolidTorusResult =
      { {1, 2, 3, 8}, {1, 3, 7, 8}, {2, 3, 6, 8},
        {2, 3, 6, 12}, {2, 6, 7, 12}, {1, 6, 7, 12},
        {1, 7, 8, 12} } := by decide

theorem zeroFiveInterfaceBistellarSolidTorusResult_card :
    zeroFiveInterfaceBistellarSolidTorusResult.card = 7 := by decide

def standardSevenVertexSolidTorusFacets : Finset (Finset (Fin 7)) :=
  { {0, 1, 3, 5}, {0, 2, 3, 5}, {1, 3, 5, 6},
    {1, 3, 4, 6}, {1, 2, 4, 6}, {0, 2, 4, 6}, {0, 2, 4, 5} }

theorem standardSevenVertexSolidTorus_f_vector :
    ((facesOfCard standardSevenVertexSolidTorusFacets 1).card,
      (facesOfCard standardSevenVertexSolidTorusFacets 2).card,
      (facesOfCard standardSevenVertexSolidTorusFacets 3).card,
      (facesOfCard standardSevenVertexSolidTorusFacets 4).card) =
      (7, 21, 21, 7) := by decide

theorem standardSevenVertexSolidTorus_boundary :
    (facesOfCard standardSevenVertexSolidTorusFacets 3).filter (fun triangle ↦
        (standardSevenVertexSolidTorusFacets.filter fun tetrahedron ↦
          triangle ∈ tetrahedron.powersetCard 3).card = 1) =
      standardSevenVertexTorusFacets := by decide

def orderedStandardSevenVertexSolidTorusFacets : Finset (Finset (Fin 7)) :=
  mapFacets centralInterfaceOrderCoordinate.symm.toEmbedding
    standardSevenVertexSolidTorusFacets

theorem map_orderedStandardSevenVertexSolidTorusFacets_coordinate :
    mapFacets centralInterfaceOrderCoordinate.toEmbedding
        orderedStandardSevenVertexSolidTorusFacets =
      standardSevenVertexSolidTorusFacets := by decide

theorem map_orderedStandardSevenVertexSolidTorusFacets_result :
    mapFacets centralInterfaceOrderEmbedding.toEmbedding
      orderedStandardSevenVertexSolidTorusFacets =
      zeroFiveInterfaceBistellarSolidTorusResult := by decide

noncomputable def zeroFiveInterfaceBistellarSolidTorusRealizationIso :
    SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 0 5)) ≅
      SSet.toTop.obj (orderedSSet zeroFiveInterfaceBistellarSolidTorusResult) :=
  bistellarMoveSequenceRealizationIso (pairwiseInterfaceFacets 0 5) 3
    zeroFiveInterfaceBistellarSolidTorusMoves
    zeroFiveInterfaceBistellarSolidTorusMoves_valid

noncomputable def orderedStandardSevenVertexSolidTorusSSetIsoResult :
    orderedSSet orderedStandardSevenVertexSolidTorusFacets ≅
      orderedSSet zeroFiveInterfaceBistellarSolidTorusResult :=
  orderedSSetMapFacetsIso centralInterfaceOrderEmbedding
      orderedStandardSevenVertexSolidTorusFacets ≪≫
    SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
      map_orderedStandardSevenVertexSolidTorusFacets_result)

noncomputable def orderedStandardSevenVertexSolidTorusCarrierHomeomorphStandard :
    facetFamilyCarrier orderedStandardSevenVertexSolidTorusFacets ≃ₜ
      facetFamilyCarrier standardSevenVertexSolidTorusFacets :=
  (facetFamilyCarrierReindexHomeomorph centralInterfaceOrderCoordinate
      orderedStandardSevenVertexSolidTorusFacets).trans
    (Homeomorph.setCongr (by
      rw [map_orderedStandardSevenVertexSolidTorusFacets_coordinate]))

noncomputable def zeroFiveInterfaceBistellarSolidTorusResultRealizationHomeomorphStandard :
    SSet.toTop.obj (orderedSSet zeroFiveInterfaceBistellarSolidTorusResult) ≃ₜ
      SSet.toTop.obj (orderedSSet standardSevenVertexSolidTorusFacets) :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso
        orderedStandardSevenVertexSolidTorusSSetIsoResult).symm).trans
    ((orderedRealizationHomeomorphFacetFamilyCarrier
        orderedStandardSevenVertexSolidTorusFacets).trans
      (orderedStandardSevenVertexSolidTorusCarrierHomeomorphStandard.trans
        (orderedRealizationHomeomorphFacetFamilyCarrier
          standardSevenVertexSolidTorusFacets).symm))

/-- The zero-five pairwise interface realizes as the classical seven-vertex, seven-tetrahedron
triangulated solid-torus model. -/
noncomputable def zeroFiveInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus :
    SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 0 5)) ≃ₜ
      SSet.toTop.obj (orderedSSet standardSevenVertexSolidTorusFacets) :=
  (TopCat.homeoOfIso zeroFiveInterfaceBistellarSolidTorusRealizationIso).trans
    zeroFiveInterfaceBistellarSolidTorusResultRealizationHomeomorphStandard

end Submission.ComplexProjectivePlaneTriangulation

