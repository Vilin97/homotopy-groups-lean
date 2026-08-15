/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfTriangulation
import Submission.ComplexProjectivePlaneTrisectionCentralTorusProductTopology

/-!
# The two solid-torus pieces of the minimal finite Hopf map

The twelve-vertex domain of the Madahar--Sarkaria map splits over the target triangle `ABC`
and its complementary disk.  This file records the two tetrahedral facet families, verifies that
they cover the domain and have the same incidence boundary, and checks their images under the
finite quotient.

The common nine-vertex boundary torus is then compared with the maintained staircase product
torus.  In the natural order on `Aᵢ,Bᵢ,Cᵢ`, exactly three edge flips suffice.  Realization
invariance and the existing point-set product comparison give an exact homeomorphism of this
common boundary with `S¹ × S¹`.

The remaining geometric step is to identify the two three-dimensional pieces themselves with
`D² × S¹` and compute the boundary gluing map in these product coordinates.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## The two preimage pieces -/

/-- The nine tetrahedra lying over the target triangle `ABC`. -/
def minimalHopfABCPreimageFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {5, 6, 9, 12}, {5, 7, 8, 13}, {5, 8, 9, 12},
    {5, 8, 11, 12}, {5, 8, 11, 13}, {6, 7, 9, 12},
    {7, 8, 10, 13}, {7, 9, 10, 13}, {7, 9, 12, 13} }

/-- The twenty-seven tetrahedra lying over the complementary target disk. -/
def minimalHopfComplementPreimageFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  minimalHopfSphereFacets \ minimalHopfABCPreimageFacets

/-- The `ABC` piece is exactly the subfamily with no `Dᵢ` vertex. -/
theorem minimalHopfABCPreimageFacets_eq_filter :
    minimalHopfABCPreimageFacets =
      minimalHopfSphereFacets.filter
        (fun facet ↦ Disjoint facet ({14, 15, 16} : Finset MinimalHopfBallVertex)) := by
  decide

/-- The two displayed pieces cover all thirty-six domain tetrahedra. -/
theorem minimalHopfPreimageFacets_union :
    minimalHopfABCPreimageFacets ∪ minimalHopfComplementPreimageFacets =
      minimalHopfSphereFacets := by
  decide

/-- The two pieces have no common top-dimensional tetrahedron. -/
theorem minimalHopfPreimageFacets_disjoint :
    Disjoint minimalHopfABCPreimageFacets minimalHopfComplementPreimageFacets := by
  decide

theorem minimalHopfABCPreimageFacets_f_vector :
    ((facesOfCard minimalHopfABCPreimageFacets 1).card,
      (facesOfCard minimalHopfABCPreimageFacets 2).card,
      (facesOfCard minimalHopfABCPreimageFacets 3).card,
      (facesOfCard minimalHopfABCPreimageFacets 4).card) =
        (9, 27, 27, 9) := by
  decide

theorem minimalHopfComplementPreimageFacets_f_vector :
    ((facesOfCard minimalHopfComplementPreimageFacets 1).card,
      (facesOfCard minimalHopfComplementPreimageFacets 2).card,
      (facesOfCard minimalHopfComplementPreimageFacets 3).card,
      (facesOfCard minimalHopfComplementPreimageFacets 4).card) =
        (12, 48, 63, 27) := by
  decide

/-- Incidence-one triangles of a tetrahedral facet family. -/
def minimalHopfTetrahedralBoundaryTriangles
    (tetrahedra : Finset (Finset MinimalHopfBallVertex)) :
    Finset (Finset MinimalHopfBallVertex) :=
  (facesOfCard tetrahedra 3).filter fun triangle ↦
    (tetrahedra.filter fun tetrahedron ↦
      triangle ∈ tetrahedron.powersetCard 3).card = 1

/-- The eighteen triangles in the common boundary of the two pieces. -/
def minimalHopfCommonTorusFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  { {5, 6, 9}, {5, 6, 12}, {5, 7, 8}, {5, 7, 13},
    {5, 8, 9}, {5, 11, 12}, {5, 11, 13}, {6, 7, 9},
    {6, 7, 12}, {7, 8, 10}, {7, 9, 10}, {7, 12, 13},
    {8, 9, 12}, {8, 10, 13}, {8, 11, 12}, {8, 11, 13},
    {9, 10, 13}, {9, 12, 13} }

/-- The incidence boundary of the `ABC` piece is the displayed common torus. -/
theorem minimalHopfABCPreimage_boundary :
    minimalHopfTetrahedralBoundaryTriangles minimalHopfABCPreimageFacets =
      minimalHopfCommonTorusFacets := by
  decide

/-- The complementary piece has exactly the same incidence boundary. -/
theorem minimalHopfComplementPreimage_boundary :
    minimalHopfTetrahedralBoundaryTriangles minimalHopfComplementPreimageFacets =
      minimalHopfCommonTorusFacets := by
  decide

/-- The common triangles are exactly the triangular faces shared by the two pieces. -/
theorem minimalHopfPreimage_common_triangles :
    facesOfCard minimalHopfABCPreimageFacets 3 ∩
        facesOfCard minimalHopfComplementPreimageFacets 3 =
      minimalHopfCommonTorusFacets := by
  decide

theorem minimalHopfCommonTorus_f_vector :
    ((facesOfCard minimalHopfCommonTorusFacets 1).card,
      (facesOfCard minimalHopfCommonTorusFacets 2).card,
      (facesOfCard minimalHopfCommonTorusFacets 3).card) =
        (9, 27, 18) := by
  decide

/-- Every edge of the common boundary belongs to exactly two boundary triangles. -/
theorem minimalHopfCommonTorus_edge_incidence_two :
    ∀ edge ∈ facesOfCard minimalHopfCommonTorusFacets 2,
      (minimalHopfCommonTorusFacets.filter fun triangle ↦
        edge ∈ triangle.powersetCard 2).card = 2 := by
  intro edge hedge
  exact (by decide : ∀ e : ↥(facesOfCard minimalHopfCommonTorusFacets 2),
    (minimalHopfCommonTorusFacets.filter fun triangle ↦
      e.1 ∈ triangle.powersetCard 2).card = 2) ⟨edge, hedge⟩

/-! ## Images in the tetrahedral target -/

/-- The `ABC` piece maps onto the single target triangle `ABC`. -/
theorem minimalHopfABCPreimage_quotient_facets :
    minimalHopfABCPreimageFacets.image
        (fun facet ↦ facet.image minimalHopfQuotientVertex) =
      {{5, 6, 7}} := by
  decide

/-- The complementary piece maps onto the three triangles forming the complementary disk. -/
theorem minimalHopfComplementPreimage_quotient_facets :
    minimalHopfComplementPreimageFacets.image
        (fun facet ↦ facet.image minimalHopfQuotientVertex) =
      {{5, 6, 8}, {5, 7, 8}, {6, 7, 8}} := by
  decide

/-- The common torus maps onto the triangular boundary of `ABC`. -/
theorem minimalHopfCommonTorus_quotient_facets :
    minimalHopfCommonTorusFacets.image
        (fun facet ↦ facet.image minimalHopfQuotientVertex) =
      {{5, 6}, {5, 7}, {6, 7}} := by
  decide

/-! ## Three flips to the staircase product torus -/

/-- The common torus after translating the consecutive vertices `5,…,13` to `Fin 9`. -/
def minimalHopfCommonTorusFinNineFacets : Finset (Finset (Fin 9)) :=
  { {0, 1, 4}, {0, 1, 7}, {0, 2, 3}, {0, 2, 8},
    {0, 3, 4}, {0, 6, 7}, {0, 6, 8}, {1, 2, 4},
    {1, 2, 7}, {2, 3, 5}, {2, 4, 5}, {2, 7, 8},
    {3, 4, 7}, {3, 5, 8}, {3, 6, 7}, {3, 6, 8},
    {4, 5, 8}, {4, 7, 8} }

/-- Increasing inclusion of the nine `Aᵢ,Bᵢ,Cᵢ` vertices into the domain type. -/
def minimalHopfABCOrderEmbedding : Fin 9 ↪o MinimalHopfBallVertex where
  toFun := ![5, 6, 7, 8, 9, 10, 11, 12, 13]
  inj' := by decide
  map_rel_iff' := by decide

theorem map_minimalHopfCommonTorusFinNineFacets :
    mapFacets minimalHopfABCOrderEmbedding.toEmbedding
        minimalHopfCommonTorusFinNineFacets =
      minimalHopfCommonTorusFacets := by
  decide

/-- Three edge flips relating the paper's common torus to the staircase product torus. -/
def minimalHopfCommonTorusToProductMoves :
    List (BistellarMoveData (Fin 9)) :=
  [⟨{2, 4}, {1, 5}⟩,
    ⟨{2, 7}, {1, 8}⟩,
    ⟨{2, 3}, {0, 5}⟩]

theorem minimalHopfCommonTorusToProductMoves_valid :
    IsValidBistellarMoveSequence minimalHopfCommonTorusFinNineFacets 2
      minimalHopfCommonTorusToProductMoves := by
  decide

theorem minimalHopfCommonTorusToProductMoves_result :
    applyBistellarMoves minimalHopfCommonTorusFinNineFacets
        minimalHopfCommonTorusToProductMoves =
      triangleBoundaryProductFacets := by
  decide

/-- Ordered reindexing identifies the actual common boundary with its `Fin 9` copy. -/
noncomputable def minimalHopfCommonTorusSSetIsoFinNine :
    orderedSSet minimalHopfCommonTorusFacets ≅
      orderedSSet minimalHopfCommonTorusFinNineFacets :=
  (orderedSSetMapFacetsIso minimalHopfABCOrderEmbedding
      minimalHopfCommonTorusFinNineFacets ≪≫
    SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex
        map_minimalHopfCommonTorusFinNineFacets)).symm

/-- Exact realization isomorphism from the common boundary to the staircase product torus. -/
noncomputable def minimalHopfCommonTorusRealizationIsoProduct :
    SSet.toTop.obj (orderedSSet minimalHopfCommonTorusFacets) ≅
      SSet.toTop.obj (orderedSSet triangleBoundaryProductFacets) :=
  SSet.toTop.mapIso minimalHopfCommonTorusSSetIsoFinNine ≪≫
    bistellarMoveSequenceRealizationIso
      minimalHopfCommonTorusFinNineFacets 2
      minimalHopfCommonTorusToProductMoves
      minimalHopfCommonTorusToProductMoves_valid ≪≫
    SSet.toTop.mapIso
      (SSet.Subcomplex.eqToIso
        (congrArg orderedSubcomplex
          minimalHopfCommonTorusToProductMoves_result))

/-- The common boundary of the two finite Hopf pieces is the exact metric product torus. -/
noncomputable def minimalHopfCommonTorusRealizationHomeomorphSphereOneProduct :
    SSet.toTop.obj (orderedSSet minimalHopfCommonTorusFacets) ≃ₜ
      SphereSpace 1 × SphereSpace 1 :=
  (TopCat.homeoOfIso minimalHopfCommonTorusRealizationIsoProduct).trans
    productTorusRealizationHomeomorphSphereOneProduct

end Submission.ComplexProjectivePlaneTriangulation
