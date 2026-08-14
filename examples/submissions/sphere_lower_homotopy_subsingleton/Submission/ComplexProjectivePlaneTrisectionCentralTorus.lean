/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.FiniteOrderedComplexCarrierReindex
import Submission.FiniteOrderedComplexCarrierHomeomorph
import Submission.ComplexProjectivePlaneTrisection

/-!
# The central trisection interface as the seven-vertex torus

The finite incidence layer identifies the common central interface with the classical periodic
seven-vertex torus pattern, but its periodic coordinate permutation is not order preserving.
We first enumerate the ambient vertices increasingly, use ordered reindexing for that embedding,
and then use the arbitrary affine carrier-reindexing homeomorphism for the periodic permutation.
The finite realization/carrier comparison composes these steps into an actual homeomorphism of
geometric realizations.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Increasing enumeration of the seven central-interface vertices. -/
def centralInterfaceOrderEmbedding : Fin 7 ↪o TrisectionVertex where
  toFun := ![1, 2, 3, 6, 7, 8, 12]
  inj' := by decide
  map_rel_iff' := by decide

/-- Change from increasing vertex order to the periodic coordinates of the standard torus. -/
def centralInterfaceOrderCoordinate : Fin 7 ≃ Fin 7 where
  toFun := ![0, 1, 3, 6, 2, 5, 4]
  invFun := ![0, 1, 4, 2, 6, 5, 3]
  left_inv := by decide
  right_inv := by decide

/-- The standard seven-vertex torus with its vertices reordered increasingly in the ambient
13-vertex complex. -/
def orderedStandardSevenVertexTorusFacets : Finset (Finset (Fin 7)) :=
  mapFacets centralInterfaceOrderCoordinate.symm.toEmbedding
    standardSevenVertexTorusFacets

theorem map_orderedStandardSevenVertexTorusFacets_coordinate :
    mapFacets centralInterfaceOrderCoordinate.toEmbedding
        orderedStandardSevenVertexTorusFacets =
      standardSevenVertexTorusFacets := by decide

theorem map_orderedStandardSevenVertexTorusFacets_central :
    mapFacets centralInterfaceOrderEmbedding.toEmbedding
        orderedStandardSevenVertexTorusFacets =
      centralInterfaceFacets := by decide

noncomputable def orderedStandardSevenVertexTorusSSetIsoCentralInterface :
    orderedSSet orderedStandardSevenVertexTorusFacets ≅
      orderedSSet centralInterfaceFacets :=
  orderedSSetMapFacetsIso centralInterfaceOrderEmbedding
      orderedStandardSevenVertexTorusFacets ≪≫
    SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
      map_orderedStandardSevenVertexTorusFacets_central)

noncomputable def orderedStandardSevenVertexTorusCarrierHomeomorphStandard :
    facetFamilyCarrier orderedStandardSevenVertexTorusFacets ≃ₜ
      facetFamilyCarrier standardSevenVertexTorusFacets :=
  (facetFamilyCarrierReindexHomeomorph centralInterfaceOrderCoordinate
      orderedStandardSevenVertexTorusFacets).trans
    (Homeomorph.setCongr (by
      rw [map_orderedStandardSevenVertexTorusFacets_coordinate]))

/-- The common central interface is homeomorphic to the canonical seven-vertex triangulated
torus. -/
noncomputable def centralInterfaceRealizationHomeomorphStandardSevenVertexTorus :
    SSet.toTop.obj (orderedSSet centralInterfaceFacets) ≃ₜ
      SSet.toTop.obj (orderedSSet standardSevenVertexTorusFacets) :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso
        orderedStandardSevenVertexTorusSSetIsoCentralInterface).symm).trans
    ((orderedRealizationHomeomorphFacetFamilyCarrier
        orderedStandardSevenVertexTorusFacets).trans
      (orderedStandardSevenVertexTorusCarrierHomeomorphStandard.trans
        (orderedRealizationHomeomorphFacetFamilyCarrier
          standardSevenVertexTorusFacets).symm))

end Submission.ComplexProjectivePlaneTriangulation

