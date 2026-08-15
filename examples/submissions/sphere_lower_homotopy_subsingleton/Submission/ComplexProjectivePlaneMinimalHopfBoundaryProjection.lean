/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfSolidTorusProjection

/-!
# Boundary compatibility of the finite Hopf solid-torus projection

The product projection on the `ABC` preimage restricts to the common boundary torus and lands in
the triangular boundary of the target face.  This file packages the four finite-complex maps and
proves that their square commutes strictly before and after geometric realization.  It is the
boundary-control datum needed for a future comparison of the two solid-torus gluings.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem minimalHopfCommonTorusFinNine_le_ABCPreimage :
    FacetFamilyLE minimalHopfCommonTorusFinNineFacets
      minimalHopfABCPreimageFinNineFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfCommonTorusFinNineFacets,
    IsFace minimalHopfABCPreimageFinNineFacets σ.1) ⟨facet, hfacet⟩

theorem triangleBoundaryThreeFacets_le_triangleThreeFacets :
    FacetFamilyLE triangleBoundaryThreeFacets triangleThreeFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥triangleBoundaryThreeFacets,
    IsFace triangleThreeFacets σ.1) ⟨facet, hfacet⟩

/-- On the common torus, the target-letter row lies in the boundary of the target triangle. -/
theorem minimalHopfABCCommonBoundaryRowFacetFamilyMapsTo :
    FacetFamilyMapsTo minimalHopfABCRowVertex
      minimalHopfCommonTorusFinNineFacets triangleBoundaryThreeFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfCommonTorusFinNineFacets,
    IsFace triangleBoundaryThreeFacets
      (σ.1.image minimalHopfABCRowVertex)) ⟨facet, hfacet⟩

def minimalHopfABCCommonBoundarySSetIncl :
    orderedSSet minimalHopfCommonTorusFinNineFacets ⟶
      orderedSSet minimalHopfABCPreimageFinNineFacets :=
  orderedSSetHomOfFacetFamilyLE minimalHopfCommonTorusFinNine_le_ABCPreimage

def minimalHopfABCTriangleBoundarySSetIncl :
    orderedSSet triangleBoundaryThreeFacets ⟶
      orderedSSet triangleThreeFacets :=
  orderedSSetHomOfFacetFamilyLE triangleBoundaryThreeFacets_le_triangleThreeFacets

def minimalHopfABCCommonBoundaryRowSSetMap :
    orderedSSet minimalHopfCommonTorusFinNineFacets ⟶
      orderedSSet triangleBoundaryThreeFacets :=
  orderedSSetMapOfMonotone minimalHopfABCRowVertex
    minimalHopfABCCommonBoundaryRowFacetFamilyMapsTo

/-- Restricting the finite quotient to the common torus commutes strictly with both inclusions. -/
theorem minimalHopfABCCommonBoundaryRow_sSet_square :
    minimalHopfABCCommonBoundarySSetIncl ≫ minimalHopfABCRowSSetMap =
      minimalHopfABCCommonBoundaryRowSSetMap ≫
        minimalHopfABCTriangleBoundarySSetIncl := by
  ext Δ x
  rfl

/-- The same boundary-restriction square commutes strictly after geometric realization. -/
theorem minimalHopfABCCommonBoundaryRow_realization_square :
    SSet.toTop.map minimalHopfABCCommonBoundarySSetIncl ≫
        SSet.toTop.map minimalHopfABCRowSSetMap =
      SSet.toTop.map minimalHopfABCCommonBoundaryRowSSetMap ≫
        SSet.toTop.map minimalHopfABCTriangleBoundarySSetIncl := by
  rw [← (SSet.toTop).map_comp, minimalHopfABCCommonBoundaryRow_sSet_square,
    (SSet.toTop).map_comp]

/-- On affine carriers, the boundary row map is the restriction of the same barycentric
pushforward used by first projection on the full solid torus. -/
theorem minimalHopfABCCommonBoundaryRow_carrier_square :
    facetFamilyCarrierHomOfFacetFamilyLE
          minimalHopfCommonTorusFinNine_le_ABCPreimage ≫
        facetFamilyCarrierHomOfMonotone minimalHopfABCRowVertex
          minimalHopfABCRowFacetFamilyMapsTo =
      facetFamilyCarrierHomOfMonotone minimalHopfABCRowVertex
          minimalHopfABCCommonBoundaryRowFacetFamilyMapsTo ≫
        facetFamilyCarrierHomOfFacetFamilyLE
          triangleBoundaryThreeFacets_le_triangleThreeFacets := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The realized boundary row map agrees with affine barycentric pushforward. -/
theorem minimalHopfABCCommonBoundaryRowRealization_projection :
    SSet.toTop.map minimalHopfABCCommonBoundaryRowSSetMap ≫
        orderedRealizationToFacetFamilyCarrier triangleBoundaryThreeFacets =
      orderedRealizationToFacetFamilyCarrier
          minimalHopfCommonTorusFinNineFacets ≫
        facetFamilyCarrierHomOfMonotone minimalHopfABCRowVertex
          minimalHopfABCCommonBoundaryRowFacetFamilyMapsTo :=
  orderedRealizationToFacetFamilyCarrier_naturality_monotone
    minimalHopfABCRowVertex minimalHopfABCCommonBoundaryRowFacetFamilyMapsTo

end Submission.ComplexProjectivePlaneTriangulation
