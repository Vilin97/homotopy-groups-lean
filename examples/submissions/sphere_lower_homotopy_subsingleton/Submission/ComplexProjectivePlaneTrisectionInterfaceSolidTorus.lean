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

/-! ## Cyclic transport to every pairwise interface -/

/-- A computable equivalence realizing the order-three trisection rotation. -/
def trisectionRotationEquiv : TrisectionVertex ≃ TrisectionVertex where
  toFun := trisectionRotationFun
  invFun := ![4, 3, 8, 7, 5, 0, 2, 1, 6, 10, 11, 9, 12]
  left_inv := by decide
  right_inv := by decide

theorem trisectionRotationEquiv_map_zeroFiveInterface :
    mapFacets trisectionRotationEquiv.toEmbedding
        (pairwiseInterfaceFacets 0 5) =
      pairwiseInterfaceFacets 5 4 := by decide

theorem trisectionRotationEquiv_map_fiveFourInterface :
    mapFacets trisectionRotationEquiv.toEmbedding
        (pairwiseInterfaceFacets 5 4) =
      pairwiseInterfaceFacets 4 0 := by decide

theorem pairwiseInterfaceFacets_comm (a b : TrisectionVertex) :
    pairwiseInterfaceFacets a b = pairwiseInterfaceFacets b a := by
  simp only [pairwiseInterfaceFacets, Finset.inter_comm]

noncomputable def orderedRealizationHomeomorphOfFacetEq
    {left right : Finset (Finset TrisectionVertex)} (h : left = right) :
    SSet.toTop.obj (orderedSSet left) ≃ₜ
      SSet.toTop.obj (orderedSSet right) :=
  TopCat.homeoOfIso (SSet.toTop.mapIso
    (SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex h)))

noncomputable def zeroFiveInterfaceRealizationHomeomorphFiveFour :
    SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 0 5)) ≃ₜ
      SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 5 4)) :=
  (orderedRealizationReindexHomeomorph trisectionRotationEquiv
      (pairwiseInterfaceFacets 0 5)).trans
    (orderedRealizationHomeomorphOfFacetEq
      trisectionRotationEquiv_map_zeroFiveInterface)

noncomputable def fiveFourInterfaceRealizationHomeomorphFourZero :
    SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 5 4)) ≃ₜ
      SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 4 0)) :=
  (orderedRealizationReindexHomeomorph trisectionRotationEquiv
      (pairwiseInterfaceFacets 5 4)).trans
    (orderedRealizationHomeomorphOfFacetEq
      trisectionRotationEquiv_map_fiveFourInterface)

noncomputable def fiveFourInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus :
    SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 5 4)) ≃ₜ
      SSet.toTop.obj (orderedSSet standardSevenVertexSolidTorusFacets) :=
  zeroFiveInterfaceRealizationHomeomorphFiveFour.symm.trans
    zeroFiveInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus

noncomputable def fourZeroInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus :
    SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 4 0)) ≃ₜ
      SSet.toTop.obj (orderedSSet standardSevenVertexSolidTorusFacets) :=
  (zeroFiveInterfaceRealizationHomeomorphFiveFour.trans
      fiveFourInterfaceRealizationHomeomorphFourZero).symm.trans
    zeroFiveInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus

noncomputable def fiveZeroInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus :
    SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 5 0)) ≃ₜ
      SSet.toTop.obj (orderedSSet standardSevenVertexSolidTorusFacets) :=
  (orderedRealizationHomeomorphOfFacetEq
      (pairwiseInterfaceFacets_comm 5 0)).trans
    zeroFiveInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus

noncomputable def fourFiveInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus :
    SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 4 5)) ≃ₜ
      SSet.toTop.obj (orderedSSet standardSevenVertexSolidTorusFacets) :=
  (orderedRealizationHomeomorphOfFacetEq
      (pairwiseInterfaceFacets_comm 4 5)).trans
    fiveFourInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus

noncomputable def zeroFourInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus :
    SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 0 4)) ≃ₜ
      SSet.toTop.obj (orderedSSet standardSevenVertexSolidTorusFacets) :=
  (orderedRealizationHomeomorphOfFacetEq
      (pairwiseInterfaceFacets_comm 0 4)).trans
    fourZeroInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus

/-- Every ordered pair of distinct trisection apexes has a pairwise-interface homeomorphism to
the standard seven-vertex triangulated solid torus. -/
theorem pairwiseInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus_nonempty
    (a : TrisectionVertex) (ha : a ∈ trisectionApexes)
    (b : TrisectionVertex) (hb : b ∈ trisectionApexes) (hab : a ≠ b) :
    Nonempty
      (SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets a b)) ≃ₜ
        SSet.toTop.obj (orderedSSet standardSevenVertexSolidTorusFacets)) := by
  have ha' : a = 0 ∨ a = 4 ∨ a = 5 := by
    simpa [trisectionApexes] using ha
  have hb' : b = 0 ∨ b = 4 ∨ b = 5 := by
    simpa [trisectionApexes] using hb
  rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl
  · exact False.elim (hab rfl)
  · exact ⟨zeroFourInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus⟩
  · exact ⟨zeroFiveInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus⟩
  · exact ⟨fourZeroInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus⟩
  · exact False.elim (hab rfl)
  · exact ⟨fourFiveInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus⟩
  · exact ⟨fiveZeroInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus⟩
  · exact ⟨fiveFourInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus⟩
  · exact False.elim (hab rfl)

/-- A chosen homeomorphism from any pairwise interface to the standard solid-torus
triangulation. -/
noncomputable def pairwiseInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus
    (a : TrisectionVertex) (ha : a ∈ trisectionApexes)
    (b : TrisectionVertex) (hb : b ∈ trisectionApexes) (hab : a ≠ b) :
    SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets a b)) ≃ₜ
      SSet.toTop.obj (orderedSSet standardSevenVertexSolidTorusFacets) :=
  (pairwiseInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus_nonempty
    a ha b hb hab).some

end Submission.ComplexProjectivePlaneTriangulation
