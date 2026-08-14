/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionCentralTorus
import Submission.BistellarSphereRealization

/-!
# The central trisection torus and the product triangulation

The classical seven-vertex torus is related by two `1–3` moves and eleven edge flips to the
standard nine-vertex triangulation obtained by taking the product of two triangular boundaries.
The complete finite certificate is checked by the Lean kernel.  Realization invariance for
bistellar moves then gives an actual homeomorphism from the central trisection interface to this
product triangulation.

The separate point-set comparison between the realization of this triangulation and the product
of the two triangular-boundary realizations is the remaining bridge to the maintained
`S¹ × S¹` model.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Increasingly embed the seven old vertices as the first seven vertices of the `3 × 3`
product grid. -/
def sevenVertexTorusProductOrderEmbedding : Fin 7 ↪o Fin 9 where
  toFun := ![0, 1, 2, 3, 4, 5, 6]
  inj' := by decide
  map_rel_iff' := by decide

/-- The seven-vertex torus, embedded in the nine-vertex product-grid vertex type. -/
def embeddedSevenVertexTorusFacets : Finset (Finset (Fin 9)) :=
  mapFacets sevenVertexTorusProductOrderEmbedding.toEmbedding
    standardSevenVertexTorusFacets

/-- The standard staircase triangulation of the product of two triangular boundaries.  Each
pair of boundary edges contributes the two triangles in its square. -/
def triangleBoundaryProductFacets : Finset (Finset (Fin 9)) :=
  { {0, 1, 4}, {0, 1, 7}, {0, 2, 5}, {0, 2, 8},
    {0, 3, 4}, {0, 3, 5}, {0, 6, 7}, {0, 6, 8},
    {1, 2, 5}, {1, 2, 8}, {1, 4, 5}, {1, 7, 8},
    {3, 4, 7}, {3, 5, 8}, {3, 6, 7}, {3, 6, 8},
    {4, 5, 8}, {4, 7, 8} }

/-- Two stellar triangle subdivisions followed by eleven edge flips transform the minimal torus
into the product triangulation. -/
def sevenVertexTorusToProductBistellarMoves :
    List (BistellarMoveData (Fin 9)) :=
  [⟨{3, 5, 6}, {8}⟩,
    ⟨{3, 4, 6}, {7}⟩,
    ⟨{4, 6}, {0, 7}⟩,
    ⟨{5, 6}, {1, 8}⟩,
    ⟨{1, 6}, {2, 8}⟩,
    ⟨{2, 6}, {0, 8}⟩,
    ⟨{0, 4}, {5, 7}⟩,
    ⟨{1, 3}, {0, 4}⟩,
    ⟨{0, 5}, {1, 7}⟩,
    ⟨{2, 3}, {0, 5}⟩,
    ⟨{1, 5}, {7, 8}⟩,
    ⟨{5, 7}, {4, 8}⟩,
    ⟨{2, 4}, {1, 5}⟩]

/-- Every displayed replacement satisfies the full two-dimensional bistellar predicate at the
state produced by the preceding replacements. -/
theorem sevenVertexTorusToProductBistellarMoves_valid :
    IsValidBistellarMoveSequence embeddedSevenVertexTorusFacets 2
      sevenVertexTorusToProductBistellarMoves := by decide

/-- The thirteen moves end at exactly the staircase product triangulation. -/
theorem sevenVertexTorusToProductBistellarMoves_result :
    applyBistellarMoves embeddedSevenVertexTorusFacets
        sevenVertexTorusToProductBistellarMoves =
      triangleBoundaryProductFacets := by decide

/-- Ordered reindexing identifies the original seven-vertex torus with its copy in the product
grid. -/
noncomputable def standardSevenVertexTorusSSetIsoEmbedded :
    orderedSSet standardSevenVertexTorusFacets ≅
      orderedSSet embeddedSevenVertexTorusFacets :=
  orderedSSetMapFacetsIso sevenVertexTorusProductOrderEmbedding
      standardSevenVertexTorusFacets ≪≫
    SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex rfl)

/-- The certified bistellar sequence identifies the embedded minimal torus realization with the
product triangulation realization. -/
noncomputable def embeddedSevenVertexTorusRealizationIsoProductTriangulation :
    SSet.toTop.obj (orderedSSet embeddedSevenVertexTorusFacets) ≅
      SSet.toTop.obj (orderedSSet triangleBoundaryProductFacets) :=
  bistellarMoveSequenceRealizationIso embeddedSevenVertexTorusFacets 2
      sevenVertexTorusToProductBistellarMoves
      sevenVertexTorusToProductBistellarMoves_valid ≪≫
    SSet.toTop.mapIso
      (SSet.Subcomplex.eqToIso
        (congrArg orderedSubcomplex sevenVertexTorusToProductBistellarMoves_result))

/-- The standard seven-vertex torus realization is homeomorphic to the canonical nine-vertex
triangulation of a product of triangular circles. -/
noncomputable def standardSevenVertexTorusRealizationHomeomorphProductTriangulation :
    SSet.toTop.obj (orderedSSet standardSevenVertexTorusFacets) ≃ₜ
      SSet.toTop.obj (orderedSSet triangleBoundaryProductFacets) :=
  TopCat.homeoOfIso
    (SSet.toTop.mapIso standardSevenVertexTorusSSetIsoEmbedded ≪≫
      embeddedSevenVertexTorusRealizationIsoProductTriangulation)

/-- The common central trisection interface is homeomorphic to the product triangulation. -/
noncomputable def centralInterfaceRealizationHomeomorphProductTriangulation :
    SSet.toTop.obj (orderedSSet centralInterfaceFacets) ≃ₜ
      SSet.toTop.obj (orderedSSet triangleBoundaryProductFacets) :=
  centralInterfaceRealizationHomeomorphStandardSevenVertexTorus.trans
    standardSevenVertexTorusRealizationHomeomorphProductTriangulation

end Submission.ComplexProjectivePlaneTriangulation
