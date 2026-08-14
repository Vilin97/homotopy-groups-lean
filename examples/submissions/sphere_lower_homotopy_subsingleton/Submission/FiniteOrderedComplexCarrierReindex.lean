/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.BistellarLocalRealization
import Submission.Cohomology.FiniteOrderedComplexReindex
import Submission.FiniteOrderedComplexCarrier
import Submission.FiniteOrderedComplexCarrierHomeomorph

/-!
# Reindexing finite affine carriers

An arbitrary equivalence of finite vertex types permutes barycentric coordinates and maps every
facet to its reindexed image. Restricting the standard-simplex coordinate homeomorphism gives a
homeomorphism of the corresponding facet-family carriers. Unlike ordered-simplicial reindexing,
this affine result does not require the equivalence to preserve the vertex order.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.FiniteOrderedComplex

variable {V W : Type} [Fintype V] [Fintype W]
  [LinearOrder V] [LinearOrder W]

/-- Reindexing every facet along an equivalence gives homeomorphic affine carriers. -/
def facetFamilyCarrierReindexHomeomorph
    (e : V ≃ W) (facets : Finset (Finset V)) :
    facetFamilyCarrier facets ≃ₜ
      facetFamilyCarrier (mapFacets e.toEmbedding facets) :=
  (stdSimplexEquivHomeomorph e).subtype fun x ↦ by
    rw [mem_facetFamilyCarrier_iff, mem_facetFamilyCarrier_iff]
    constructor
    · rintro ⟨facet, hfacet, hsupport⟩
      refine ⟨facet.map e.toEmbedding,
        Finset.mem_map.mpr ⟨facet, hfacet, rfl⟩, ?_⟩
      intro w hw
      rw [stdSimplexEquivHomeomorph_apply_apply]
      apply hsupport
      intro hv
      apply hw
      exact Finset.mem_map.mpr ⟨e.symm w, hv, e.apply_symm_apply w⟩
    · rintro ⟨mappedFacet, hmappedFacet, hsupport⟩
      obtain ⟨facet, hfacet, rfl⟩ := Finset.mem_map.mp hmappedFacet
      refine ⟨facet, hfacet, ?_⟩
      intro v hv
      have hzero := hsupport (e v) (by
        intro hmem
        obtain ⟨u, hu, heu⟩ := Finset.mem_map.mp hmem
        exact hv (e.injective heu ▸ hu))
      rw [stdSimplexEquivHomeomorph_apply_apply, e.symm_apply_apply] at hzero
      exact hzero

/-- Arbitrary vertex reindexing preserves the geometric realization of a finite facet family,
even when the equivalence is not order preserving. -/
noncomputable def orderedRealizationReindexHomeomorph
    (e : V ≃ W) (facets : Finset (Finset V)) :
    SSet.toTop.obj (orderedSSet facets) ≃ₜ
      SSet.toTop.obj (orderedSSet (mapFacets e.toEmbedding facets)) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier facets).trans
    ((facetFamilyCarrierReindexHomeomorph e facets).trans
      (orderedRealizationHomeomorphFacetFamilyCarrier
        (mapFacets e.toEmbedding facets)).symm)

end Submission.FiniteOrderedComplex
