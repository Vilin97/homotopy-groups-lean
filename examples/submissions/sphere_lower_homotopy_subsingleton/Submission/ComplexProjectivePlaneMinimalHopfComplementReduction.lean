/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfSolidTorusProduct

/-!
# Relative reduction of the complementary finite Hopf piece

The complementary preimage piece has twenty-seven tetrahedra and three interior vertices.
Thirteen explicit relative three-dimensional bistellar moves remove two of those vertices and
reduce the piece to eighteen tetrahedra.  The boundary is unchanged.  The remaining interior
vertex has the eight-triangle octahedral sphere as its link.

This isolates the still-needed solid-torus comparison to one explicit octahedral interior star.
The link is independently certified as a two-sphere by three bistellar moves.  Four lifted moves
also replace the eight-tetrahedron cone star by a four-tetrahedron ball with the same octahedral
boundary; this local replacement is valid even though its first new diagonal is blocked in the
ambient complementary complex.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## Reindexing the complementary piece -/

/-- The complementary piece on the consecutive twelve domain vertices, translated to `Fin 12`. -/
def minimalHopfComplementPreimageFinTwelveFacets : Finset (Finset (Fin 12)) :=
  { {0, 1, 4, 11}, {0, 1, 7, 11}, {0, 2, 3, 10},
    {0, 2, 8, 10}, {0, 3, 4, 10}, {0, 4, 9, 10},
    {0, 4, 9, 11}, {0, 6, 7, 11}, {0, 6, 8, 11},
    {0, 8, 9, 10}, {0, 8, 9, 11}, {1, 2, 4, 11},
    {1, 2, 7, 11}, {2, 3, 5, 11}, {2, 3, 10, 11},
    {2, 4, 5, 11}, {2, 7, 8, 10}, {2, 7, 10, 11},
    {3, 4, 7, 10}, {3, 5, 8, 11}, {3, 6, 7, 11},
    {3, 6, 8, 11}, {3, 7, 10, 11}, {4, 5, 8, 11},
    {4, 7, 8, 10}, {4, 8, 9, 10}, {4, 8, 9, 11} }

/-- Increasing inclusion of the twelve vertices `Aᵢ,Bᵢ,Cᵢ,Dᵢ` into the domain type. -/
def minimalHopfSphereOrderEmbedding : Fin 12 ↪o MinimalHopfBallVertex where
  toFun := ![5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  inj' := by decide
  map_rel_iff' := by decide

theorem map_minimalHopfComplementPreimageFinTwelveFacets :
    mapFacets minimalHopfSphereOrderEmbedding.toEmbedding
        minimalHopfComplementPreimageFinTwelveFacets =
      minimalHopfComplementPreimageFacets := by
  decide

/-- Ordered reindexing identifies the actual complementary piece with its `Fin 12` copy. -/
noncomputable def minimalHopfComplementPreimageSSetIsoFinTwelve :
    orderedSSet minimalHopfComplementPreimageFacets ≅
      orderedSSet minimalHopfComplementPreimageFinTwelveFacets :=
  (orderedSSetMapFacetsIso minimalHopfSphereOrderEmbedding
      minimalHopfComplementPreimageFinTwelveFacets ≪≫
    SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex
        map_minimalHopfComplementPreimageFinTwelveFacets)).symm

/-! ## Thirteen relative moves -/

/-- A relative bistellar reduction removing vertices `9` and `11` and retaining vertex `10`. -/
def minimalHopfComplementReductionMoves :
    List (BistellarMoveData (Fin 12)) :=
  [⟨{9, 10}, {0, 4, 8}⟩,
    ⟨{9}, {0, 4, 8, 11}⟩,
    ⟨{10, 11}, {2, 3, 7}⟩,
    ⟨{4, 8, 11}, {0, 5}⟩,
    ⟨{0, 4, 11}, {1, 5}⟩,
    ⟨{0, 1, 11}, {5, 7}⟩,
    ⟨{0, 7, 11}, {5, 6}⟩,
    ⟨{0, 11}, {5, 6, 8}⟩,
    ⟨{4, 11}, {1, 2, 5}⟩,
    ⟨{1, 11}, {2, 5, 7}⟩,
    ⟨{2, 11}, {3, 5, 7}⟩,
    ⟨{7, 11}, {3, 5, 6}⟩,
    ⟨{11}, {3, 5, 6, 8}⟩]

theorem minimalHopfComplementReductionMoves_valid :
    IsValidBistellarMoveSequence
      minimalHopfComplementPreimageFinTwelveFacets 3
      minimalHopfComplementReductionMoves := by
  decide

/-- The eighteen-tetrahedron endpoint with one interior vertex. -/
def minimalHopfComplementReducedFacets : Finset (Finset (Fin 12)) :=
  { {0, 1, 4, 5}, {0, 1, 5, 7}, {0, 2, 3, 10},
    {0, 2, 8, 10}, {0, 3, 4, 10}, {0, 4, 5, 8},
    {0, 4, 8, 10}, {0, 5, 6, 7}, {0, 5, 6, 8},
    {1, 2, 4, 5}, {1, 2, 5, 7}, {2, 3, 5, 7},
    {2, 3, 7, 10}, {2, 7, 8, 10}, {3, 4, 7, 10},
    {3, 5, 6, 7}, {3, 5, 6, 8}, {4, 7, 8, 10} }

theorem minimalHopfComplementReductionMoves_result :
    applyBistellarMoves minimalHopfComplementPreimageFinTwelveFacets
        minimalHopfComplementReductionMoves =
      minimalHopfComplementReducedFacets := by
  decide

theorem minimalHopfComplementReduced_f_vector :
    ((facesOfCard minimalHopfComplementReducedFacets 1).card,
      (facesOfCard minimalHopfComplementReducedFacets 2).card,
      (facesOfCard minimalHopfComplementReducedFacets 3).card,
      (facesOfCard minimalHopfComplementReducedFacets 4).card) =
        (10, 37, 45, 18) := by
  decide

/-- Exact realization invariance along the thirteen relative moves. -/
noncomputable def minimalHopfComplementRealizationIsoReduced :
    SSet.toTop.obj (orderedSSet minimalHopfComplementPreimageFacets) ≅
      SSet.toTop.obj (orderedSSet minimalHopfComplementReducedFacets) :=
  SSet.toTop.mapIso minimalHopfComplementPreimageSSetIsoFinTwelve ≪≫
    bistellarMoveSequenceRealizationIso
      minimalHopfComplementPreimageFinTwelveFacets 3
      minimalHopfComplementReductionMoves
      minimalHopfComplementReductionMoves_valid ≪≫
    SSet.toTop.mapIso
      (SSet.Subcomplex.eqToIso
        (congrArg orderedSubcomplex
          minimalHopfComplementReductionMoves_result))

/-! ## The unchanged common boundary -/

/-- The common torus on the first nine vertices of `Fin 12`. -/
def minimalHopfCommonTorusFinTwelveFacets : Finset (Finset (Fin 12)) :=
  { {0, 1, 4}, {0, 1, 7}, {0, 2, 3}, {0, 2, 8},
    {0, 3, 4}, {0, 6, 7}, {0, 6, 8}, {1, 2, 4},
    {1, 2, 7}, {2, 3, 5}, {2, 4, 5}, {2, 7, 8},
    {3, 4, 7}, {3, 5, 8}, {3, 6, 7}, {3, 6, 8},
    {4, 5, 8}, {4, 7, 8} }

/-- Incidence-one triangles of a tetrahedral family on `Fin 12`. -/
def finTwelveTetrahedralBoundaryTriangles
    (tetrahedra : Finset (Finset (Fin 12))) : Finset (Finset (Fin 12)) :=
  (facesOfCard tetrahedra 3).filter fun triangle ↦
    (tetrahedra.filter fun tetrahedron ↦
      triangle ∈ tetrahedron.powersetCard 3).card = 1

theorem minimalHopfComplementReduced_boundary :
    finTwelveTetrahedralBoundaryTriangles minimalHopfComplementReducedFacets =
      minimalHopfCommonTorusFinTwelveFacets := by
  decide

/-! ## The remaining octahedral interior star -/

/-- The eight tetrahedra incident to the remaining interior vertex `10`. -/
def minimalHopfComplementReducedInteriorStarFacets :
    Finset (Finset (Fin 12)) :=
  { {0, 2, 3, 10}, {0, 2, 8, 10}, {0, 3, 4, 10},
    {0, 4, 8, 10}, {2, 3, 7, 10}, {2, 7, 8, 10},
    {3, 4, 7, 10}, {4, 7, 8, 10} }

theorem minimalHopfComplementReducedInteriorStarFacets_eq_filter :
    minimalHopfComplementReducedFacets.filter (fun facet ↦ 10 ∈ facet) =
      minimalHopfComplementReducedInteriorStarFacets := by
  decide

/-- The octahedral two-sphere forming the link of the remaining interior vertex. -/
def minimalHopfComplementReducedInteriorLinkFacets :
    Finset (Finset (Fin 12)) :=
  { {0, 2, 3}, {0, 2, 8}, {0, 3, 4}, {0, 4, 8},
    {2, 3, 7}, {2, 7, 8}, {3, 4, 7}, {4, 7, 8} }

theorem minimalHopfComplementReducedInteriorStar_is_cone :
    minimalHopfComplementReducedInteriorLinkFacets.image
        (fun facet ↦ insert 10 facet) =
      minimalHopfComplementReducedInteriorStarFacets := by
  decide

theorem minimalHopfComplementReducedInteriorStar_boundary :
    finTwelveTetrahedralBoundaryTriangles
        minimalHopfComplementReducedInteriorStarFacets =
      minimalHopfComplementReducedInteriorLinkFacets := by
  decide

/-- One flip and two vertex removals reduce the octahedral link to a tetrahedron boundary. -/
def minimalHopfComplementReducedInteriorLinkMoves :
    List (BistellarMoveData (Fin 12)) :=
  [⟨{0, 2}, {3, 8}⟩,
    ⟨{0}, {3, 4, 8}⟩,
    ⟨{2}, {3, 7, 8}⟩]

theorem minimalHopfComplementReducedInteriorLinkMoves_valid :
    IsValidBistellarMoveSequence
      minimalHopfComplementReducedInteriorLinkFacets 2
      minimalHopfComplementReducedInteriorLinkMoves := by
  decide

theorem minimalHopfComplementReducedInteriorLinkMoves_result :
    applyBistellarMoves minimalHopfComplementReducedInteriorLinkFacets
        minimalHopfComplementReducedInteriorLinkMoves =
      simplexBoundaryFacets ({3, 4, 7, 8} : Finset (Fin 12)) := by
  decide

theorem minimalHopfComplementReducedInteriorLink_isBistellarSphere :
    IsBistellarSphere minimalHopfComplementReducedInteriorLinkFacets 2 :=
  ⟨minimalHopfComplementReducedInteriorLinkMoves,
    {3, 4, 7, 8}, by decide,
    minimalHopfComplementReducedInteriorLinkMoves_valid,
    minimalHopfComplementReducedInteriorLinkMoves_result⟩

/-- The remaining interior link realizes as the exact metric two-sphere. -/
theorem minimalHopfComplementReducedInteriorLink_nonempty_homeomorphSphereTwo :
    Nonempty
      (SSet.toTop.obj
          (orderedSSet minimalHopfComplementReducedInteriorLinkFacets) ≃ₜ
        SphereSpace 2) :=
  minimalHopfComplementReducedInteriorLink_isBistellarSphere
    |>.nonempty_realizationHomeomorphSphere

/-! ## A local four-move replacement of the octahedral cone -/

/-- Lift the three link moves through the cone and then remove its apex. -/
def minimalHopfComplementReducedInteriorStarMoves :
    List (BistellarMoveData (Fin 12)) :=
  [⟨{0, 2, 10}, {3, 8}⟩,
    ⟨{0, 10}, {3, 4, 8}⟩,
    ⟨{2, 10}, {3, 7, 8}⟩,
    ⟨{10}, {3, 4, 7, 8}⟩]

theorem minimalHopfComplementReducedInteriorStarMoves_valid :
    IsValidBistellarMoveSequence
      minimalHopfComplementReducedInteriorStarFacets 3
      minimalHopfComplementReducedInteriorStarMoves := by
  decide

/-- A four-tetrahedron ball filling the same octahedral boundary along diagonal `{3,8}`. -/
def minimalHopfComplementReducedInteriorStarReplacementFacets :
    Finset (Finset (Fin 12)) :=
  { {0, 2, 3, 8}, {0, 3, 4, 8},
    {2, 3, 7, 8}, {3, 4, 7, 8} }

theorem minimalHopfComplementReducedInteriorStarMoves_result :
    applyBistellarMoves minimalHopfComplementReducedInteriorStarFacets
        minimalHopfComplementReducedInteriorStarMoves =
      minimalHopfComplementReducedInteriorStarReplacementFacets := by
  decide

theorem minimalHopfComplementReducedInteriorStarReplacement_boundary :
    finTwelveTetrahedralBoundaryTriangles
        minimalHopfComplementReducedInteriorStarReplacementFacets =
      minimalHopfComplementReducedInteriorLinkFacets := by
  decide

noncomputable def minimalHopfComplementReducedInteriorStarRealizationIsoReplacement :
    SSet.toTop.obj
        (orderedSSet minimalHopfComplementReducedInteriorStarFacets) ≅
      SSet.toTop.obj
        (orderedSSet minimalHopfComplementReducedInteriorStarReplacementFacets) :=
  bistellarMoveSequenceRealizationIso
      minimalHopfComplementReducedInteriorStarFacets 3
      minimalHopfComplementReducedInteriorStarMoves
      minimalHopfComplementReducedInteriorStarMoves_valid ≪≫
    SSet.toTop.mapIso
      (SSet.Subcomplex.eqToIso
        (congrArg orderedSubcomplex
          minimalHopfComplementReducedInteriorStarMoves_result))

end Submission.ComplexProjectivePlaneTriangulation
