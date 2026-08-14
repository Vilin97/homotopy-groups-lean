/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisection
import Submission.BistellarSphereRealization

/-!
# Bistellar simplification of a projective-plane trisection piece

An explicit sequence of nine `3–2` moves and four `4–1` moves simplifies the 26-tetrahedron base
of the trisection piece at vertex `0` to the boundary of a four-simplex.  Move validity and the final
facet equality are finite kernel-checked certificates.  Their PL-topological interpretation awaits
the general realization-invariance theorem for bistellar moves.
-/

namespace Submission

namespace ComplexProjectivePlaneTriangulation

open CategoryTheory Simplicial FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-- Thirteen reducing bistellar moves from the 26-tetrahedron base to a simplex boundary. -/
def trisectionPieceZeroBaseBistellarMoves : List (BistellarMoveData TrisectionVertex) :=
  [⟨{3, 9}, {2, 6, 12}⟩,
    ⟨{2, 9}, {6, 7, 12}⟩,
    ⟨{8, 9}, {1, 7, 12}⟩,
    ⟨{9}, {1, 6, 7, 12}⟩,
    ⟨{7, 10}, {2, 8, 12}⟩,
    ⟨{2, 7}, {6, 8, 12}⟩,
    ⟨{2, 6}, {3, 8, 12}⟩,
    ⟨{1, 2}, {3, 8, 10}⟩,
    ⟨{2}, {3, 8, 10, 12}⟩,
    ⟨{3, 7}, {1, 6, 8}⟩,
    ⟨{7}, {1, 6, 8, 12}⟩,
    ⟨{1, 3}, {6, 8, 10}⟩,
    ⟨{1}, {6, 8, 10, 12}⟩]

/-- Every displayed replacement satisfies the full local bistellar-move predicate at the state
produced by the preceding replacements. -/
theorem trisectionPieceZeroBaseBistellarMoves_valid :
    IsValidBistellarMoveSequence (trisectionPieceBaseFacets 0) 3
      trisectionPieceZeroBaseBistellarMoves := by decide

/-- Every move is strictly reducing: the removed family has more facets than the inserted family. -/
theorem trisectionPieceZeroBaseBistellarMoves_reducing :
    ∀ move ∈ trisectionPieceZeroBaseBistellarMoves,
      move.oldCore.card < move.newCore.card := by decide

/-- The thirteen moves end at exactly the five tetrahedra bounding the four-simplex on the
displayed vertex set. -/
theorem trisectionPieceZeroBase_bistellar_result :
    applyBistellarMoves (trisectionPieceBaseFacets 0)
        trisectionPieceZeroBaseBistellarMoves =
      simplexBoundaryFacets {3, 6, 8, 10, 12} := by decide

/-- The final bistellar facet family has the expected boundary f-vector. -/
theorem trisectionPieceZeroBase_bistellar_result_f_vector :
    let result := applyBistellarMoves (trisectionPieceBaseFacets 0)
      trisectionPieceZeroBaseBistellarMoves
    ((facesOfCard result 1).card, (facesOfCard result 2).card,
      (facesOfCard result 3).card, (facesOfCard result 4).card) = (5, 10, 10, 5) := by decide

/-- The base at apex `0` is a bistellar three-sphere in the executable combinatorial sense. -/
theorem trisectionPieceZeroBase_isBistellarThreeSphere :
    IsBistellarSphere (trisectionPieceBaseFacets 0) 3 :=
  ⟨trisectionPieceZeroBaseBistellarMoves, {3, 6, 8, 10, 12}, by decide,
    trisectionPieceZeroBaseBistellarMoves_valid,
    trisectionPieceZeroBase_bistellar_result⟩

/-- Rotate both cores of one bistellar move. -/
def rotateBistellarMoveData (move : BistellarMoveData TrisectionVertex) :
    BistellarMoveData TrisectionVertex :=
  ⟨move.oldCore.image trisectionRotationFun,
    move.newCore.image trisectionRotationFun⟩

/-- The once-rotated reduction sequence for the base at apex `5`. -/
def trisectionPieceFiveBaseBistellarMoves : List (BistellarMoveData TrisectionVertex) :=
  trisectionPieceZeroBaseBistellarMoves.map rotateBistellarMoveData

/-- The twice-rotated reduction sequence for the base at apex `4`. -/
def trisectionPieceFourBaseBistellarMoves : List (BistellarMoveData TrisectionVertex) :=
  trisectionPieceFiveBaseBistellarMoves.map rotateBistellarMoveData

/-- The once-rotated sequence is valid on the base at apex `5`. -/
theorem trisectionPieceFiveBaseBistellarMoves_valid :
    IsValidBistellarMoveSequence (trisectionPieceBaseFacets 5) 3
      trisectionPieceFiveBaseBistellarMoves := by decide

/-- The once-rotated sequence ends at an explicit four-simplex boundary. -/
theorem trisectionPieceFiveBase_bistellar_result :
    applyBistellarMoves (trisectionPieceBaseFacets 5)
        trisectionPieceFiveBaseBistellarMoves =
      simplexBoundaryFacets {1, 2, 8, 9, 12} := by decide

/-- The base at apex `5` is a bistellar three-sphere. -/
theorem trisectionPieceFiveBase_isBistellarThreeSphere :
    IsBistellarSphere (trisectionPieceBaseFacets 5) 3 :=
  ⟨trisectionPieceFiveBaseBistellarMoves, {1, 2, 8, 9, 12}, by decide,
    trisectionPieceFiveBaseBistellarMoves_valid,
    trisectionPieceFiveBase_bistellar_result⟩

/-- The twice-rotated sequence is valid on the base at apex `4`. -/
theorem trisectionPieceFourBaseBistellarMoves_valid :
    IsValidBistellarMoveSequence (trisectionPieceBaseFacets 4) 3
      trisectionPieceFourBaseBistellarMoves := by decide

/-- The twice-rotated sequence ends at an explicit four-simplex boundary. -/
theorem trisectionPieceFourBase_bistellar_result :
    applyBistellarMoves (trisectionPieceBaseFacets 4)
        trisectionPieceFourBaseBistellarMoves =
      simplexBoundaryFacets {2, 6, 7, 11, 12} := by decide

/-- The base at apex `4` is a bistellar three-sphere. -/
theorem trisectionPieceFourBase_isBistellarThreeSphere :
    IsBistellarSphere (trisectionPieceBaseFacets 4) 3 :=
  ⟨trisectionPieceFourBaseBistellarMoves, {2, 6, 7, 11, 12}, by decide,
    trisectionPieceFourBaseBistellarMoves_valid,
    trisectionPieceFourBase_bistellar_result⟩

/-- All three trisection-piece bases are certified bistellar three-spheres. -/
theorem trisectionPieceBases_areBistellarThreeSpheres :
    IsBistellarSphere (trisectionPieceBaseFacets 0) 3 ∧
      IsBistellarSphere (trisectionPieceBaseFacets 5) 3 ∧
      IsBistellarSphere (trisectionPieceBaseFacets 4) 3 :=
  ⟨trisectionPieceZeroBase_isBistellarThreeSphere,
    trisectionPieceFiveBase_isBistellarThreeSphere,
    trisectionPieceFourBase_isBistellarThreeSphere⟩

/-! ## Identification of the computed endpoints -/

/-- The increasing enumeration of the five vertices in the base-at-zero endpoint boundary. -/
def trisectionPieceZeroBoundaryVertexEmbedding : Fin 5 ↪o TrisectionVertex where
  toFun := ![3, 6, 8, 10, 12]
  inj' := by decide
  map_rel_iff' := by decide

/-- The increasing enumeration of the five vertices in the once-rotated endpoint boundary. -/
def trisectionPieceFiveBoundaryVertexEmbedding : Fin 5 ↪o TrisectionVertex where
  toFun := ![1, 2, 8, 9, 12]
  inj' := by decide
  map_rel_iff' := by decide

/-- The increasing enumeration of the five vertices in the twice-rotated endpoint boundary. -/
def trisectionPieceFourBoundaryVertexEmbedding : Fin 5 ↪o TrisectionVertex where
  toFun := ![2, 6, 7, 11, 12]
  inj' := by decide
  map_rel_iff' := by decide

/-- Reindexing the standard five-vertex boundary gives the endpoint at apex `0`. -/
theorem map_standard_boundary_facets_zero :
    mapFacets trisectionPieceZeroBoundaryVertexEmbedding.toEmbedding
        (simplexBoundaryFacets (Finset.univ : Finset (Fin 5))) =
      simplexBoundaryFacets ({3, 6, 8, 10, 12} : Finset TrisectionVertex) := by
  decide

/-- Reindexing the standard five-vertex boundary gives the endpoint at apex `5`. -/
theorem map_standard_boundary_facets_five :
    mapFacets trisectionPieceFiveBoundaryVertexEmbedding.toEmbedding
        (simplexBoundaryFacets (Finset.univ : Finset (Fin 5))) =
      simplexBoundaryFacets ({1, 2, 8, 9, 12} : Finset TrisectionVertex) := by
  decide

/-- Reindexing the standard five-vertex boundary gives the endpoint at apex `4`. -/
theorem map_standard_boundary_facets_four :
    mapFacets trisectionPieceFourBoundaryVertexEmbedding.toEmbedding
        (simplexBoundaryFacets (Finset.univ : Finset (Fin 5))) =
      simplexBoundaryFacets ({2, 6, 7, 11, 12} : Finset TrisectionVertex) := by
  decide

/-- The endpoint boundary at apex `0` is the standard ordered five-vertex boundary. -/
noncomputable def trisectionPieceZeroFinalBoundarySSetIso :
    orderedSSet (simplexBoundaryFacets (Finset.univ : Finset (Fin 5))) ≅
      orderedSSet (simplexBoundaryFacets ({3, 6, 8, 10, 12} : Finset TrisectionVertex)) :=
  orderedSSetMapFacetsIso trisectionPieceZeroBoundaryVertexEmbedding _ ≪≫
    SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex map_standard_boundary_facets_zero)

/-- The endpoint boundary at apex `5` is the standard ordered five-vertex boundary. -/
noncomputable def trisectionPieceFiveFinalBoundarySSetIso :
    orderedSSet (simplexBoundaryFacets (Finset.univ : Finset (Fin 5))) ≅
      orderedSSet (simplexBoundaryFacets ({1, 2, 8, 9, 12} : Finset TrisectionVertex)) :=
  orderedSSetMapFacetsIso trisectionPieceFiveBoundaryVertexEmbedding _ ≪≫
    SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex map_standard_boundary_facets_five)

/-- The endpoint boundary at apex `4` is the standard ordered five-vertex boundary. -/
noncomputable def trisectionPieceFourFinalBoundarySSetIso :
    orderedSSet (simplexBoundaryFacets (Finset.univ : Finset (Fin 5))) ≅
      orderedSSet (simplexBoundaryFacets ({2, 6, 7, 11, 12} : Finset TrisectionVertex)) :=
  orderedSSetMapFacetsIso trisectionPieceFourBoundaryVertexEmbedding _ ≪≫
    SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex map_standard_boundary_facets_four)

/-- The endpoint boundary of the base-at-zero reduction is the standard simplicial three-sphere. -/
noncomputable def trisectionPieceZeroFinalBoundarySSetIsoStd :
    orderedSSet
        (simplexBoundaryFacets ({3, 6, 8, 10, 12} : Finset TrisectionVertex)) ≅
      (SSet.boundary 4 : SSet) :=
  trisectionPieceZeroFinalBoundarySSetIso.symm ≪≫
    (boundaryOrderedSSetIso 4).symm

/-- The endpoint boundary of the base-at-five reduction is the standard simplicial three-sphere. -/
noncomputable def trisectionPieceFiveFinalBoundarySSetIsoStd :
    orderedSSet
        (simplexBoundaryFacets ({1, 2, 8, 9, 12} : Finset TrisectionVertex)) ≅
      (SSet.boundary 4 : SSet) :=
  trisectionPieceFiveFinalBoundarySSetIso.symm ≪≫
    (boundaryOrderedSSetIso 4).symm

/-- The endpoint boundary of the base-at-four reduction is the standard simplicial three-sphere. -/
noncomputable def trisectionPieceFourFinalBoundarySSetIsoStd :
    orderedSSet
        (simplexBoundaryFacets ({2, 6, 7, 11, 12} : Finset TrisectionVertex)) ≅
      (SSet.boundary 4 : SSet) :=
  trisectionPieceFourFinalBoundarySSetIso.symm ≪≫
    (boundaryOrderedSSetIso 4).symm

/-- The facet family computed after all thirteen moves is isomorphic to the standard simplicial
three-sphere.  This identifies the endpoint only; invariance under each bistellar move is the
separate next bridge. -/
noncomputable def trisectionPieceZeroBistellarResultSSetIso :
    orderedSSet
        (applyBistellarMoves (trisectionPieceBaseFacets 0)
          trisectionPieceZeroBaseBistellarMoves) ≅
      (SSet.boundary 4 : SSet) :=
  SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex trisectionPieceZeroBase_bistellar_result) ≪≫
    trisectionPieceZeroFinalBoundarySSetIsoStd

/-- The once-rotated computed endpoint is the standard simplicial three-sphere. -/
noncomputable def trisectionPieceFiveBistellarResultSSetIso :
    orderedSSet
        (applyBistellarMoves (trisectionPieceBaseFacets 5)
          trisectionPieceFiveBaseBistellarMoves) ≅
      (SSet.boundary 4 : SSet) :=
  SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex trisectionPieceFiveBase_bistellar_result) ≪≫
    trisectionPieceFiveFinalBoundarySSetIsoStd

/-- The twice-rotated computed endpoint is the standard simplicial three-sphere. -/
noncomputable def trisectionPieceFourBistellarResultSSetIso :
    orderedSSet
        (applyBistellarMoves (trisectionPieceBaseFacets 4)
          trisectionPieceFourBaseBistellarMoves) ≅
      (SSet.boundary 4 : SSet) :=
  SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex trisectionPieceFourBase_bistellar_result) ≪≫
    trisectionPieceFourFinalBoundarySSetIsoStd

/-- Geometric realization of the base-at-zero computed endpoint is isomorphic to realization of
the standard simplicial three-sphere. -/
noncomputable def trisectionPieceZeroBistellarResultRealizationIso :
    SSet.toTop.obj
        (orderedSSet
          (applyBistellarMoves (trisectionPieceBaseFacets 0)
            trisectionPieceZeroBaseBistellarMoves)) ≅
      SSet.toTop.obj (SSet.boundary 4 : SSet) :=
  SSet.toTop.mapIso trisectionPieceZeroBistellarResultSSetIso

/-- Geometric realization of the once-rotated computed endpoint is the realization of the
standard simplicial three-sphere. -/
noncomputable def trisectionPieceFiveBistellarResultRealizationIso :
    SSet.toTop.obj
        (orderedSSet
          (applyBistellarMoves (trisectionPieceBaseFacets 5)
            trisectionPieceFiveBaseBistellarMoves)) ≅
      SSet.toTop.obj (SSet.boundary 4 : SSet) :=
  SSet.toTop.mapIso trisectionPieceFiveBistellarResultSSetIso

/-- Geometric realization of the twice-rotated computed endpoint is the realization of the
standard simplicial three-sphere. -/
noncomputable def trisectionPieceFourBistellarResultRealizationIso :
    SSet.toTop.obj
        (orderedSSet
          (applyBistellarMoves (trisectionPieceBaseFacets 4)
            trisectionPieceFourBaseBistellarMoves)) ≅
      SSet.toTop.obj (SSet.boundary 4 : SSet) :=
  SSet.toTop.mapIso trisectionPieceFourBistellarResultSSetIso

/-- The realized base-at-zero endpoint maps canonically to the exact metric three-sphere. -/
noncomputable def trisectionPieceZeroBistellarResultRealizationToSphere :
    SSet.toTop.obj
        (orderedSSet
          (applyBistellarMoves (trisectionPieceBaseFacets 0)
            trisectionPieceZeroBaseBistellarMoves)) ⟶
      TopCat.of (SphereSpace 3) :=
  trisectionPieceZeroBistellarResultRealizationIso.hom ≫
    boundaryRealizationToSphere 3

/-- The realized once-rotated endpoint maps canonically to the exact metric three-sphere. -/
noncomputable def trisectionPieceFiveBistellarResultRealizationToSphere :
    SSet.toTop.obj
        (orderedSSet
          (applyBistellarMoves (trisectionPieceBaseFacets 5)
            trisectionPieceFiveBaseBistellarMoves)) ⟶
      TopCat.of (SphereSpace 3) :=
  trisectionPieceFiveBistellarResultRealizationIso.hom ≫
    boundaryRealizationToSphere 3

/-- The realized twice-rotated endpoint maps canonically to the exact metric three-sphere. -/
noncomputable def trisectionPieceFourBistellarResultRealizationToSphere :
    SSet.toTop.obj
        (orderedSSet
          (applyBistellarMoves (trisectionPieceBaseFacets 4)
            trisectionPieceFourBaseBistellarMoves)) ⟶
      TopCat.of (SphereSpace 3) :=
  trisectionPieceFourBistellarResultRealizationIso.hom ≫
    boundaryRealizationToSphere 3

/-- The realized base-at-zero computed endpoint is homeomorphic to the exact metric
three-sphere. -/
noncomputable def trisectionPieceZeroBistellarResultRealizationHomeomorphSphere :
    SSet.toTop.obj
        (orderedSSet
          (applyBistellarMoves (trisectionPieceBaseFacets 0)
            trisectionPieceZeroBaseBistellarMoves)) ≃ₜ
      SphereSpace 3 :=
  (TopCat.homeoOfIso trisectionPieceZeroBistellarResultRealizationIso).trans
    (boundaryRealizationHomeomorphSphere 3)

/-- The realized once-rotated computed endpoint is homeomorphic to the exact metric
three-sphere. -/
noncomputable def trisectionPieceFiveBistellarResultRealizationHomeomorphSphere :
    SSet.toTop.obj
        (orderedSSet
          (applyBistellarMoves (trisectionPieceBaseFacets 5)
            trisectionPieceFiveBaseBistellarMoves)) ≃ₜ
      SphereSpace 3 :=
  (TopCat.homeoOfIso trisectionPieceFiveBistellarResultRealizationIso).trans
    (boundaryRealizationHomeomorphSphere 3)

/-- The realized twice-rotated computed endpoint is homeomorphic to the exact metric
three-sphere. -/
noncomputable def trisectionPieceFourBistellarResultRealizationHomeomorphSphere :
    SSet.toTop.obj
        (orderedSSet
          (applyBistellarMoves (trisectionPieceBaseFacets 4)
            trisectionPieceFourBaseBistellarMoves)) ≃ₜ
      SphereSpace 3 :=
  (TopCat.homeoOfIso trisectionPieceFourBistellarResultRealizationIso).trans
    (boundaryRealizationHomeomorphSphere 3)

@[simp]
theorem trisectionPieceZeroBistellarResultRealizationHomeomorphSphere_apply
    (x : SSet.toTop.obj
      (orderedSSet
        (applyBistellarMoves (trisectionPieceBaseFacets 0)
          trisectionPieceZeroBaseBistellarMoves))) :
    trisectionPieceZeroBistellarResultRealizationHomeomorphSphere x =
      trisectionPieceZeroBistellarResultRealizationToSphere x := by
  rfl

@[simp]
theorem trisectionPieceFiveBistellarResultRealizationHomeomorphSphere_apply
    (x : SSet.toTop.obj
      (orderedSSet
        (applyBistellarMoves (trisectionPieceBaseFacets 5)
          trisectionPieceFiveBaseBistellarMoves))) :
    trisectionPieceFiveBistellarResultRealizationHomeomorphSphere x =
      trisectionPieceFiveBistellarResultRealizationToSphere x := by
  rfl

@[simp]
theorem trisectionPieceFourBistellarResultRealizationHomeomorphSphere_apply
    (x : SSet.toTop.obj
      (orderedSSet
        (applyBistellarMoves (trisectionPieceBaseFacets 4)
          trisectionPieceFourBaseBistellarMoves))) :
    trisectionPieceFourBistellarResultRealizationHomeomorphSphere x =
      trisectionPieceFourBistellarResultRealizationToSphere x := by
  rfl

/-- The canonical map from the realized base-at-zero computed endpoint onto the exact metric
three-sphere is surjective. -/
theorem trisectionPieceZeroBistellarResultRealizationToSphere_surjective :
    Function.Surjective trisectionPieceZeroBistellarResultRealizationToSphere := by
  exact (boundaryRealizationToSphere_surjective 3).comp
    (ConcreteCategory.bijective_of_isIso
      trisectionPieceZeroBistellarResultRealizationIso.hom).2

/-- The canonical map from the realized once-rotated computed endpoint onto the exact metric
three-sphere is surjective. -/
theorem trisectionPieceFiveBistellarResultRealizationToSphere_surjective :
    Function.Surjective trisectionPieceFiveBistellarResultRealizationToSphere := by
  exact (boundaryRealizationToSphere_surjective 3).comp
    (ConcreteCategory.bijective_of_isIso
      trisectionPieceFiveBistellarResultRealizationIso.hom).2

/-- The canonical map from the realized twice-rotated computed endpoint onto the exact metric
three-sphere is surjective. -/
theorem trisectionPieceFourBistellarResultRealizationToSphere_surjective :
    Function.Surjective trisectionPieceFourBistellarResultRealizationToSphere := by
  exact (boundaryRealizationToSphere_surjective 3).comp
    (ConcreteCategory.bijective_of_isIso
      trisectionPieceFourBistellarResultRealizationIso.hom).2

end ComplexProjectivePlaneTriangulation

end Submission
