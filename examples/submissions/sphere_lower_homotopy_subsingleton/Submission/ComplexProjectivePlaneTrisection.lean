/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTriangulation

/-!
# The combinatorial trisection of the nine-vertex projective plane

This file records the symmetry-breaking subdivision used in the trisection proof for the
nine-vertex projective-plane complex.  In the vertex convention of
`ComplexProjectivePlaneTriangulation`, the three distinguished vertices are `0`, `4`, and `5`.
We add barycentres for their three edges and their triangle, numbered `9`, `10`, `11`, and `12`.

The resulting 78 four-simplices split into three collections of 26.  Each collection is a
combinatorial cone.  Any two cones meet in a 13-tetrahedron interface, and the boundary of every
pairwise interface is the same 14-triangle central closed surface.  All statements here are exact
finite incidence certificates; no topological ball, solid-torus, or torus identification is
asserted yet.
-/

namespace Submission

namespace ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

/-- Vertices of the symmetry-breaking subdivision: nine old vertices and four barycentres. -/
abbrev TrisectionVertex := Fin 13

/-- The old vertices represented by a subdivision vertex.  Vertices `9`, `10`, and `11` are the
three edge barycentres, and vertex `12` is the triangle barycentre. -/
def trisectionVertexCarrier : TrisectionVertex → Finset Vertex :=
  ![{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}, {8},
    {0, 5}, {0, 4}, {4, 5}, {0, 4, 5}]

/-- The old vertices carried by a subdivided simplex. -/
def trisectionSimplexCarrier (σ : Finset TrisectionVertex) : Finset Vertex :=
  σ.biUnion trisectionVertexCarrier

/-- The 78 four-simplices in the symmetry-breaking subdivision. -/
def trisectionSubdivisionFacets : Finset (Finset TrisectionVertex) :=
  { {0, 1, 2, 3, 8}, {0, 1, 2, 3, 10}, {0, 1, 2, 8, 10},
    {0, 1, 3, 6, 7}, {0, 1, 3, 6, 10}, {0, 1, 3, 7, 8},
    {0, 1, 6, 7, 9}, {0, 1, 6, 9, 12}, {0, 1, 6, 10, 12},
    {0, 1, 7, 8, 9}, {0, 1, 8, 9, 12}, {0, 1, 8, 10, 12},
    {0, 2, 3, 6, 8}, {0, 2, 3, 6, 9}, {0, 2, 3, 9, 12},
    {0, 2, 3, 10, 12}, {0, 2, 6, 7, 8}, {0, 2, 6, 7, 9},
    {0, 2, 7, 8, 10}, {0, 2, 7, 9, 12}, {0, 2, 7, 10, 12},
    {0, 3, 6, 7, 8}, {0, 3, 6, 9, 12}, {0, 3, 6, 10, 12},
    {0, 7, 8, 9, 12}, {0, 7, 8, 10, 12},
    {1, 2, 3, 4, 7}, {1, 2, 3, 4, 10}, {1, 2, 3, 5, 7},
    {1, 2, 3, 5, 8}, {1, 2, 4, 6, 7}, {1, 2, 4, 6, 8},
    {1, 2, 4, 8, 10}, {1, 2, 5, 6, 7}, {1, 2, 5, 6, 8},
    {1, 3, 4, 6, 7}, {1, 3, 4, 6, 10}, {1, 3, 5, 7, 8},
    {1, 4, 6, 8, 11}, {1, 4, 6, 10, 12}, {1, 4, 6, 11, 12},
    {1, 4, 8, 10, 12}, {1, 4, 8, 11, 12}, {1, 5, 6, 7, 9},
    {1, 5, 6, 8, 11}, {1, 5, 6, 9, 12}, {1, 5, 6, 11, 12},
    {1, 5, 7, 8, 9}, {1, 5, 8, 9, 12}, {1, 5, 8, 11, 12},
    {2, 3, 4, 7, 11}, {2, 3, 4, 10, 12}, {2, 3, 4, 11, 12},
    {2, 3, 5, 6, 8}, {2, 3, 5, 6, 9}, {2, 3, 5, 7, 11},
    {2, 3, 5, 9, 12}, {2, 3, 5, 11, 12}, {2, 4, 6, 7, 8},
    {2, 4, 7, 8, 10}, {2, 4, 7, 10, 12}, {2, 4, 7, 11, 12},
    {2, 5, 6, 7, 9}, {2, 5, 7, 9, 12}, {2, 5, 7, 11, 12},
    {3, 4, 6, 7, 8}, {3, 4, 6, 8, 11}, {3, 4, 6, 10, 12},
    {3, 4, 6, 11, 12}, {3, 4, 7, 8, 11}, {3, 5, 6, 8, 11},
    {3, 5, 6, 9, 12}, {3, 5, 6, 11, 12}, {3, 5, 7, 8, 11},
    {4, 7, 8, 10, 12}, {4, 7, 8, 11, 12},
    {5, 7, 8, 9, 12}, {5, 7, 8, 11, 12} }

/-- The original distinguished triangle in the nine-vertex labeling. -/
def originalTrisectionVertices : Finset Vertex := {0, 4, 5}

/-- The three old vertices serving as the cone points of the subdivided trisection. -/
def trisectionApexes : Finset TrisectionVertex := {0, 4, 5}

/-- The order-three symmetry of the subdivided complex. -/
def trisectionRotationFun : TrisectionVertex → TrisectionVertex :=
  ![5, 7, 6, 1, 0, 4, 8, 3, 2, 11, 9, 10, 12]

/-- The rotation as a computable vertex embedding. -/
def trisectionRotationEmbedding : TrisectionVertex ↪ TrisectionVertex :=
  ⟨trisectionRotationFun, by decide⟩

/-- The order-three symmetry as a permutation of subdivision vertices. -/
noncomputable def trisectionRotation : TrisectionVertex ≃ TrisectionVertex :=
  Equiv.ofBijective trisectionRotationFun (by decide)

/-- Applying the displayed vertex rotation three times fixes every subdivision vertex. -/
theorem trisectionRotationFun_order_three :
    ∀ v, trisectionRotationFun
      (trisectionRotationFun (trisectionRotationFun v)) = v := by decide

/-- The original facets have the expected rank distribution relative to the distinguished
triangle: 18 of rank one, 12 of rank two, and 6 of rank three. -/
theorem originalFacet_rank_distribution :
    ((facets.filter fun σ ↦ (σ ∩ originalTrisectionVertices).card = 1).card,
      (facets.filter fun σ ↦ (σ ∩ originalTrisectionVertices).card = 2).card,
      (facets.filter fun σ ↦ (σ ∩ originalTrisectionVertices).card = 3).card) =
      (18, 12, 6) := by decide

/-- The subdivision contains exactly 78 distinct four-simplices. -/
theorem trisectionSubdivisionFacets_card : trisectionSubdivisionFacets.card = 78 := by decide

/-- Every subdivided top simplex has five vertices. -/
theorem trisectionSubdivisionFacets_pure :
    ∀ σ ∈ trisectionSubdivisionFacets, σ.card = 5 := by
  intro σ hσ
  exact (by decide : ∀ τ : ↥trisectionSubdivisionFacets, τ.1.card = 5) ⟨σ, hσ⟩

/-- Collapsing the four new barycentric vertices recovers exactly the 36 old facets. -/
theorem trisectionSimplexCarrier_image :
    trisectionSubdivisionFacets.image trisectionSimplexCarrier = facets := by decide

/-- Every subdivided facet contains exactly one of the three cone vertices. -/
theorem trisectionSubdivisionFacet_unique_apex :
    ∀ σ ∈ trisectionSubdivisionFacets, (σ ∩ trisectionApexes).card = 1 := by
  intro σ hσ
  exact (by decide : ∀ τ : ↥trisectionSubdivisionFacets,
    (τ.1 ∩ trisectionApexes).card = 1) ⟨σ, hσ⟩

/-- The subdivision facet list is invariant under the order-three rotation. -/
theorem trisectionRotation_facets :
    trisectionSubdivisionFacets.map
        (Finset.mapEmbedding trisectionRotationEmbedding).toEmbedding =
      trisectionSubdivisionFacets := by decide

/-- The top-dimensional simplices assigned to one trisection cone. -/
def trisectionPieceFacets (a : TrisectionVertex) : Finset (Finset TrisectionVertex) :=
  trisectionSubdivisionFacets.filter fun σ ↦ a ∈ σ

/-- Each of the three trisection pieces consists of 26 four-simplices. -/
theorem trisectionPieceFacets_card :
    ∀ a ∈ trisectionApexes, (trisectionPieceFacets a).card = 26 := by
  intro a ha
  exact (by decide : ∀ b : ↥trisectionApexes, (trisectionPieceFacets b.1).card = 26) ⟨a, ha⟩

/-- The three trisection pieces cover all subdivided top simplices. -/
theorem trisectionPieceFacets_cover :
    trisectionPieceFacets 0 ∪ trisectionPieceFacets 4 ∪ trisectionPieceFacets 5 =
      trisectionSubdivisionFacets := by decide

/-- The rotation cyclically permutes the three trisection pieces. -/
theorem trisectionRotation_pieceFacets :
    (trisectionPieceFacets 0).map
        (Finset.mapEmbedding trisectionRotationEmbedding).toEmbedding =
        trisectionPieceFacets 5 ∧
      (trisectionPieceFacets 5).map
          (Finset.mapEmbedding trisectionRotationEmbedding).toEmbedding =
        trisectionPieceFacets 4 ∧
      (trisectionPieceFacets 4).map
          (Finset.mapEmbedding trisectionRotationEmbedding).toEmbedding =
        trisectionPieceFacets 0 := by decide

/-- The facets opposite an apex form the base of its combinatorial cone. -/
def trisectionPieceBaseFacets (a : TrisectionVertex) : Finset (Finset TrisectionVertex) :=
  (trisectionPieceFacets a).image fun σ ↦ σ.erase a

/-- Every trisection piece is exactly the cone on its opposite tetrahedra. -/
theorem trisectionPieceFacets_isCone :
    ∀ a ∈ trisectionApexes,
      (trisectionPieceBaseFacets a).image (fun σ ↦ insert a σ) =
        trisectionPieceFacets a := by
  intro a ha
  exact (by decide : ∀ b : ↥trisectionApexes,
    (trisectionPieceBaseFacets b.1).image (fun σ ↦ insert b.1 σ) =
      trisectionPieceFacets b.1) ⟨a, ha⟩

/-- Every cone base has f-vector `(9,35,52,26)`. -/
theorem trisectionPieceBase_f_vector :
    ∀ a ∈ trisectionApexes,
      ((facesOfCard (trisectionPieceBaseFacets a) 1).card,
        (facesOfCard (trisectionPieceBaseFacets a) 2).card,
        (facesOfCard (trisectionPieceBaseFacets a) 3).card,
        (facesOfCard (trisectionPieceBaseFacets a) 4).card) =
        (9, 35, 52, 26) := by
  intro a ha
  exact (by decide : ∀ b : ↥trisectionApexes,
    ((facesOfCard (trisectionPieceBaseFacets b.1) 1).card,
      (facesOfCard (trisectionPieceBaseFacets b.1) 2).card,
      (facesOfCard (trisectionPieceBaseFacets b.1) 3).card,
      (facesOfCard (trisectionPieceBaseFacets b.1) 4).card) =
      (9, 35, 52, 26)) ⟨a, ha⟩

/-- Every triangle of a cone base belongs to exactly two tetrahedra. -/
theorem trisectionPieceBase_triangle_incidence_two :
    ∀ a ∈ trisectionApexes, ∀ τ ∈ facesOfCard (trisectionPieceBaseFacets a) 3,
      ((trisectionPieceBaseFacets a).filter fun σ ↦ τ ∈ σ.powersetCard 3).card = 2 := by
  intro a ha τ hτ
  exact (by decide : ∀ b : ↥trisectionApexes,
    ∀ ρ : ↥(facesOfCard (trisectionPieceBaseFacets b.1) 3),
      ((trisectionPieceBaseFacets b.1).filter
        fun σ ↦ ρ.1 ∈ σ.powersetCard 3).card = 2) ⟨a, ha⟩ ⟨τ, hτ⟩

/-- The tetrahedra common to two trisection pieces. -/
def pairwiseInterfaceFacets (a b : TrisectionVertex) :
    Finset (Finset TrisectionVertex) :=
  facesOfCard (trisectionPieceFacets a) 4 ∩ facesOfCard (trisectionPieceFacets b) 4

/-- Every pairwise interface has f-vector `(8,28,33,13)`. -/
theorem pairwiseInterface_f_vector :
    ∀ a ∈ trisectionApexes, ∀ b ∈ trisectionApexes, a ≠ b →
      ((facesOfCard (pairwiseInterfaceFacets a b) 1).card,
        (facesOfCard (pairwiseInterfaceFacets a b) 2).card,
        (facesOfCard (pairwiseInterfaceFacets a b) 3).card,
        (facesOfCard (pairwiseInterfaceFacets a b) 4).card) =
        (8, 28, 33, 13) := by decide

/-- Join of two finite families of facets. -/
def joinFacetFamilies (left right : Finset (Finset TrisectionVertex)) :
    Finset (Finset TrisectionVertex) :=
  left.biUnion fun σ ↦ right.image fun τ ↦ σ ∪ τ

/-- The three-tetrahedron part of the interface between the pieces at `0` and `5`. -/
def zeroFiveInterfaceBallOneFacets : Finset (Finset TrisectionVertex) :=
  { {1, 3, 7, 8}, {1, 2, 3, 8}, {2, 3, 6, 8} }

/-- The ten-tetrahedron part of the interface between the pieces at `0` and `5`. -/
def zeroFiveInterfaceBallTwoFacets : Finset (Finset TrisectionVertex) :=
  { {1, 6, 7, 9}, {2, 6, 7, 9}, {1, 7, 8, 9}, {2, 3, 6, 9},
    {1, 6, 9, 12}, {3, 6, 9, 12}, {2, 3, 9, 12}, {2, 7, 9, 12},
    {7, 8, 9, 12}, {1, 8, 9, 12} }

/-- The pairwise interface is the union of its three- and ten-tetrahedron pieces. -/
theorem zeroFiveInterface_ball_decomposition :
    zeroFiveInterfaceBallOneFacets ∪ zeroFiveInterfaceBallTwoFacets =
      pairwiseInterfaceFacets 0 5 := by decide

/-- The three-tetrahedron piece is the simplicial join of a three-edge path and an edge. -/
theorem zeroFiveInterfaceBallOne_eq_join :
    zeroFiveInterfaceBallOneFacets =
      joinFacetFamilies {{7, 1}, {1, 2}, {2, 6}} {{3, 8}} := by decide

/-- The triangle family serving as the base of the ten-tetrahedron cone. -/
def zeroFiveInterfaceBallTwoBaseFacets : Finset (Finset TrisectionVertex) :=
  zeroFiveInterfaceBallTwoFacets.image fun σ ↦ σ.erase 9

/-- The ten-tetrahedron piece is the cone at vertex `9` on its base triangles. -/
theorem zeroFiveInterfaceBallTwo_isCone :
    zeroFiveInterfaceBallTwoBaseFacets.image (fun σ ↦ insert 9 σ) =
      zeroFiveInterfaceBallTwoFacets := by decide

/-- The base of the ten-tetrahedron cone has f-vector `(7,15,10)`. -/
theorem zeroFiveInterfaceBallTwoBase_f_vector :
    ((facesOfCard zeroFiveInterfaceBallTwoBaseFacets 1).card,
      (facesOfCard zeroFiveInterfaceBallTwoBaseFacets 2).card,
      (facesOfCard zeroFiveInterfaceBallTwoBaseFacets 3).card) = (7, 15, 10) := by decide

/-- Every edge in the base of the ten-tetrahedron cone belongs to exactly two triangles. -/
theorem zeroFiveInterfaceBallTwoBase_edge_incidence_two :
    ∀ e ∈ facesOfCard zeroFiveInterfaceBallTwoBaseFacets 2,
      (zeroFiveInterfaceBallTwoBaseFacets.filter fun σ ↦ e ∈ σ.powersetCard 2).card = 2 := by
  intro e he
  exact (by decide : ∀ τ : ↥(facesOfCard zeroFiveInterfaceBallTwoBaseFacets 2),
    (zeroFiveInterfaceBallTwoBaseFacets.filter
      fun σ ↦ τ.1 ∈ σ.powersetCard 2).card = 2) ⟨e, he⟩

/-- The two tetrahedral pieces meet in precisely two disjoint triangles. -/
theorem zeroFiveInterface_ball_intersection :
    facesOfCard zeroFiveInterfaceBallOneFacets 3 ∩
      facesOfCard zeroFiveInterfaceBallTwoFacets 3 =
        {{1, 7, 8}, {2, 3, 6}} := by decide

/-- The two gluing triangles in the pairwise-interface decomposition are vertex-disjoint. -/
theorem zeroFiveInterface_gluingTriangles_disjoint :
    Disjoint ({1, 7, 8} : Finset TrisectionVertex) {2, 3, 6} := by decide

/-- Boundary triangles of a finite tetrahedral complex, detected by incidence one. -/
def tetrahedralBoundaryTriangles (tetrahedra : Finset (Finset TrisectionVertex)) :
    Finset (Finset TrisectionVertex) :=
  (facesOfCard tetrahedra 3).filter fun τ ↦
    (tetrahedra.filter fun σ ↦ τ ∈ σ.powersetCard 3).card = 1

/-- The common 14-triangle central interface of the three pieces. -/
def centralInterfaceFacets : Finset (Finset TrisectionVertex) :=
  facesOfCard (trisectionPieceFacets 0) 3 ∩
    facesOfCard (trisectionPieceFacets 4) 3 ∩
      facesOfCard (trisectionPieceFacets 5) 3

/-- The boundary of every pairwise interface is the common central interface. -/
theorem pairwiseInterface_boundary_eq_central :
    ∀ a ∈ trisectionApexes, ∀ b ∈ trisectionApexes, a ≠ b →
      tetrahedralBoundaryTriangles (pairwiseInterfaceFacets a b) = centralInterfaceFacets := by
  decide

/-- The central interface has the seven-vertex f-vector `(7,21,14)`. -/
theorem centralInterface_f_vector :
    ((facesOfCard centralInterfaceFacets 1).card,
      (facesOfCard centralInterfaceFacets 2).card,
      (facesOfCard centralInterfaceFacets 3).card) = (7, 21, 14) := by decide

/-- Every central edge belongs to exactly two central triangles. -/
theorem centralInterface_edge_incidence_two :
    ∀ e ∈ facesOfCard centralInterfaceFacets 2,
      (centralInterfaceFacets.filter fun σ ↦ e ∈ σ.powersetCard 2).card = 2 := by
  intro e he
  exact (by decide : ∀ τ : ↥(facesOfCard centralInterfaceFacets 2),
    (centralInterfaceFacets.filter fun σ ↦ τ.1 ∈ σ.powersetCard 2).card = 2) ⟨e, he⟩

/-- The seven vertices occurring in the central interface. -/
def centralInterfaceVertices : Finset TrisectionVertex :=
  centralInterfaceFacets.biUnion fun σ ↦ σ

/-- Periodic coordinates on the seven central vertices. -/
def centralInterfaceCoordinate : TrisectionVertex → Fin 7 :=
  ![0, 0, 1, 3, 0, 0, 6, 2, 5, 0, 0, 0, 4]

/-- The standard periodic 14-triangle pattern on seven vertices. -/
def standardSevenVertexTorusFacets : Finset (Finset (Fin 7)) :=
  { {0, 1, 3}, {0, 1, 5}, {0, 2, 3}, {0, 2, 6}, {0, 4, 5}, {0, 4, 6},
    {1, 2, 4}, {1, 2, 6}, {1, 3, 4}, {1, 5, 6}, {2, 3, 5}, {2, 4, 5},
    {3, 4, 6}, {3, 5, 6} }

/-- The central vertex set is exactly the displayed seven-element set. -/
theorem centralInterfaceVertices_eq :
    centralInterfaceVertices = {1, 2, 3, 6, 7, 8, 12} := by decide

/-- Periodic coordinates are injective on the central vertices. -/
theorem centralInterfaceCoordinate_injective :
    ∀ a ∈ centralInterfaceVertices, ∀ b ∈ centralInterfaceVertices,
      centralInterfaceCoordinate a = centralInterfaceCoordinate b → a = b := by decide

/-- Relabeling by periodic coordinates identifies the central interface with the standard
seven-vertex, fourteen-triangle torus pattern. -/
theorem centralInterface_image_eq_standardSevenVertexTorus :
    centralInterfaceFacets.image (fun σ ↦ σ.image centralInterfaceCoordinate) =
      standardSevenVertexTorusFacets := by decide

end ComplexProjectivePlaneTriangulation

end Submission
