/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfSolidTorusProduct

/-!
# The finite Hopf quotient is projection on the product solid torus

The nine-tetrahedron preimage of the target face `ABC` is already identified with the product of
a full triangle and a triangular circle.  This file proves compatibility with the finite Hopf
map: after translating its nine vertices to `Fin 9`, the simplicial quotient is the row map, and
its geometric realization is exactly first-factor projection under the affine product
homeomorphism.

The proof uses naturality of the canonical realization/carrier homeomorphism for monotone maps
that may identify vertices.  Thus the compatibility is an equality of continuous maps, not only
a homotopy-class statement.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Collapse each consecutive triple of the nine product vertices to its target-letter row. -/
def minimalHopfABCRowVertex : Fin 9 →o Fin 3 where
  toFun := ![0, 0, 0, 1, 1, 1, 2, 2, 2]
  monotone' := by decide

/-- Increasing coordinates for the actual target vertices `A,B,C`. -/
def minimalHopfABCTargetOrderEmbedding : Fin 3 ↪o Vertex where
  toFun := ![5, 6, 7]
  inj' := by decide
  map_rel_iff' := by decide

/-- The row map is exactly the finite Hopf quotient after reindexing both source and target. -/
theorem minimalHopfABCRowVertex_reindexes_quotient (v : Fin 9) :
    minimalHopfQuotientVertex (minimalHopfABCOrderEmbedding v) =
      minimalHopfABCTargetOrderEmbedding (minimalHopfABCRowVertex v) := by
  fin_cases v <;> decide

theorem minimalHopfABCRowFacetFamilyMapsTo :
    FacetFamilyMapsTo minimalHopfABCRowVertex
      minimalHopfABCPreimageFinNineFacets triangleThreeFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfABCPreimageFinNineFacets,
    IsFace triangleThreeFacets (σ.1.image minimalHopfABCRowVertex))
      ⟨facet, hfacet⟩

/-- The row simplicial map on the reindexed `ABC` preimage. -/
def minimalHopfABCRowSSetMap :
    orderedSSet minimalHopfABCPreimageFinNineFacets ⟶
      orderedSSet triangleThreeFacets :=
  orderedSSetMapOfMonotone minimalHopfABCRowVertex
    minimalHopfABCRowFacetFamilyMapsTo

/-- First-factor projection from the affine product model of the `ABC` piece. -/
def minimalHopfABCSolidTorusCarrierProjection :
    C(MinimalHopfABCSolidTorusCarrier, TriangleThreeCarrier) where
  toFun x := (minimalHopfABCSolidTorusCarrierToProduct x).1
  continuous_toFun :=
    continuous_fst.comp continuous_minimalHopfABCSolidTorusCarrierToProduct

/-- Affine pushforward along the finite quotient is literally the target-letter marginal. -/
theorem minimalHopfABCRowCarrierMap_eq_projection
    (x : MinimalHopfABCSolidTorusCarrier) :
    facetFamilyCarrierMapOfMonotone minimalHopfABCRowVertex
        minimalHopfABCRowFacetFamilyMapsTo x =
      minimalHopfABCSolidTorusCarrierProjection x := by
  have hcoord (i : Fin 3) :
      stdSimplex.map minimalHopfABCRowVertex x.1 i =
        minimalHopfABCSolidTorusRowCoord x i := by
    have hfilter :
        (Finset.univ.filter fun z : Fin 9 ↦
          minimalHopfABCRowVertex z = i) =
        ![({0, 1, 2} : Finset (Fin 9)), {3, 4, 5}, {6, 7, 8}] i := by
      fin_cases i <;> decide
    simp only [stdSimplex.map_coe]
    rw [FunOnFinite.linearMap_apply_apply]
    rw [hfilter]
    rw [show (x.1 : Fin 9 → ℝ) = x.1.1 by rfl]
    fin_cases i <;> simp [minimalHopfABCSolidTorusRowCoord] <;> ring
  apply Subtype.ext
  change stdSimplex.map minimalHopfABCRowVertex x.1 =
    minimalHopfABCSolidTorusRowSimplex x
  apply Subtype.ext
  exact funext hcoord

theorem minimalHopfABCRowCarrierHom_eq_projection :
    facetFamilyCarrierHomOfMonotone minimalHopfABCRowVertex
        minimalHopfABCRowFacetFamilyMapsTo =
      TopCat.ofHom minimalHopfABCSolidTorusCarrierProjection := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact minimalHopfABCRowCarrierMap_eq_projection x

/-- Under the explicit carrier product homeomorphism, the same map is first projection. -/
theorem minimalHopfABCSolidTorusCarrierProjection_eq_fst :
    minimalHopfABCSolidTorusCarrierProjection =
      (ContinuousMap.fst :
        C(TriangleThreeCarrier × TriangleBoundaryThreeCarrier,
          TriangleThreeCarrier)).comp
        ⟨minimalHopfABCSolidTorusCarrierHomeomorphProduct,
          minimalHopfABCSolidTorusCarrierHomeomorphProduct.continuous⟩ := by
  ext x
  rfl

/-- The realized finite quotient on the `ABC` piece commutes strictly with first projection from
its product carrier model. -/
theorem minimalHopfABCRowRealization_projection :
    SSet.toTop.map minimalHopfABCRowSSetMap ≫
        orderedRealizationToFacetFamilyCarrier triangleThreeFacets =
      orderedRealizationToFacetFamilyCarrier
          minimalHopfABCPreimageFinNineFacets ≫
        TopCat.ofHom minimalHopfABCSolidTorusCarrierProjection := by
  rw [← minimalHopfABCRowCarrierHom_eq_projection]
  exact orderedRealizationToFacetFamilyCarrier_naturality_monotone
    minimalHopfABCRowVertex minimalHopfABCRowFacetFamilyMapsTo

end Submission.ComplexProjectivePlaneTriangulation
