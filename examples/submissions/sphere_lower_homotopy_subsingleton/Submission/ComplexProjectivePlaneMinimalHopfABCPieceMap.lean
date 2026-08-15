/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfComplementMap

/-!
# The actual `ABC` piece of the finite Hopf map

The first-factor projection theorem for the nine-tetrahedron solid torus is naturally stated
after reindexing its vertices by `Fin 9` and the target face by `Fin 3`.  This file packages the
corresponding map on the actual finite Hopf source and target vertex types.  It proves strict
reindexing, ambient, and common-boundary squares, providing the `ABC` half of the same gluing
diagram as the complementary map of pairs.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The single target face `ABC` on the actual projective-plane vertex type. -/
def minimalHopfABCTargetFacets : Finset (Finset Vertex) :=
  {{5, 6, 7}}

theorem map_triangleThreeFacets_minimalHopfABCTargetOrderEmbedding :
    mapFacets minimalHopfABCTargetOrderEmbedding.toEmbedding triangleThreeFacets =
      minimalHopfABCTargetFacets := by
  decide

theorem map_triangleBoundaryThreeFacets_minimalHopfABCTargetOrderEmbedding :
    mapFacets minimalHopfABCTargetOrderEmbedding.toEmbedding
        triangleBoundaryThreeFacets =
      minimalHopfTargetBoundaryFacets := by
  decide

/-- Ordered reindexing of the actual target face by `Fin 3`. -/
noncomputable def minimalHopfABCTargetSSetIsoFinThree :
    orderedSSet minimalHopfABCTargetFacets ≅
      orderedSSet triangleThreeFacets :=
  (orderedSSetMapFacetsIso minimalHopfABCTargetOrderEmbedding
      triangleThreeFacets ≪≫
    SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex
        map_triangleThreeFacets_minimalHopfABCTargetOrderEmbedding)).symm

/-- Ordered reindexing of the actual triangular target boundary by `Fin 3`. -/
noncomputable def minimalHopfTargetBoundarySSetIsoFinThree :
    orderedSSet minimalHopfTargetBoundaryFacets ≅
      orderedSSet triangleBoundaryThreeFacets :=
  (orderedSSetMapFacetsIso minimalHopfABCTargetOrderEmbedding
      triangleBoundaryThreeFacets ≪≫
    SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex
        map_triangleBoundaryThreeFacets_minimalHopfABCTargetOrderEmbedding)).symm

theorem minimalHopfABCFacetFamilyMapsTo :
    FacetFamilyMapsTo minimalHopfQuotientVertex
      minimalHopfABCPreimageFacets minimalHopfABCTargetFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfABCPreimageFacets,
    IsFace minimalHopfABCTargetFacets
      (σ.1.image minimalHopfQuotientVertex)) ⟨facet, hfacet⟩

theorem minimalHopfABCPreimageFacets_le_sphere :
    FacetFamilyLE minimalHopfABCPreimageFacets minimalHopfSphereFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfABCPreimageFacets,
    IsFace minimalHopfSphereFacets σ.1) ⟨facet, hfacet⟩

theorem minimalHopfABCTargetFacets_le_target :
    FacetFamilyLE minimalHopfABCTargetFacets minimalHopfTargetFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfABCTargetFacets,
    IsFace minimalHopfTargetFacets σ.1) ⟨facet, hfacet⟩

theorem minimalHopfCommonTorusFacets_le_ABC :
    FacetFamilyLE minimalHopfCommonTorusFacets minimalHopfABCPreimageFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfCommonTorusFacets,
    IsFace minimalHopfABCPreimageFacets σ.1) ⟨facet, hfacet⟩

theorem minimalHopfTargetBoundaryFacets_le_ABC :
    FacetFamilyLE minimalHopfTargetBoundaryFacets minimalHopfABCTargetFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfTargetBoundaryFacets,
    IsFace minimalHopfABCTargetFacets σ.1) ⟨facet, hfacet⟩

def minimalHopfABCSSetMap :
    orderedSSet minimalHopfABCPreimageFacets ⟶
      orderedSSet minimalHopfABCTargetFacets :=
  orderedSSetMapOfMonotone minimalHopfQuotientVertex
    minimalHopfABCFacetFamilyMapsTo

def minimalHopfABCSSetInclSphere :
    orderedSSet minimalHopfABCPreimageFacets ⟶
      orderedSSet minimalHopfSphereFacets :=
  orderedSSetHomOfFacetFamilyLE minimalHopfABCPreimageFacets_le_sphere

def minimalHopfABCTargetSSetInclTarget :
    orderedSSet minimalHopfABCTargetFacets ⟶
      orderedSSet minimalHopfTargetFacets :=
  orderedSSetHomOfFacetFamilyLE minimalHopfABCTargetFacets_le_target

def minimalHopfCommonBoundarySSetInclABC :
    orderedSSet minimalHopfCommonTorusFacets ⟶
      orderedSSet minimalHopfABCPreimageFacets :=
  orderedSSetHomOfFacetFamilyLE minimalHopfCommonTorusFacets_le_ABC

def minimalHopfTargetBoundarySSetInclABC :
    orderedSSet minimalHopfTargetBoundaryFacets ⟶
      orderedSSet minimalHopfABCTargetFacets :=
  orderedSSetHomOfFacetFamilyLE minimalHopfTargetBoundaryFacets_le_ABC

/-- The reindexed row map is exactly the actual finite Hopf restriction. -/
theorem minimalHopfABC_reindex_sSet_square :
    minimalHopfABCPreimageSSetIsoFinNine.inv ≫ minimalHopfABCSSetMap =
      minimalHopfABCRowSSetMap ≫ minimalHopfABCTargetSSetIsoFinThree.inv := by
  ext Δ x
  apply Subtype.ext
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  simp [minimalHopfABCPreimageSSetIsoFinNine,
    minimalHopfABCTargetSSetIsoFinThree,
    minimalHopfABCSSetMap, minimalHopfABCRowSSetMap,
    orderedSSetMapFacetsIso]
  change minimalHopfQuotientVertex
      (minimalHopfABCOrderEmbedding (x.1.obj i)) =
    minimalHopfABCTargetOrderEmbedding
      (minimalHopfABCRowVertex (x.1.obj i))
  exact minimalHopfABCRowVertex_reindexes_quotient (x.1.obj i)

/-- The same reindexing square, oriented from the actual complexes to their consecutive finite
coordinate types. -/
theorem minimalHopfABC_reindex_sSet_square_hom :
    minimalHopfABCSSetMap ≫ minimalHopfABCTargetSSetIsoFinThree.hom =
      minimalHopfABCPreimageSSetIsoFinNine.hom ≫
        minimalHopfABCRowSSetMap := by
  calc
    _ = (minimalHopfABCPreimageSSetIsoFinNine.hom ≫
          minimalHopfABCPreimageSSetIsoFinNine.inv) ≫
        minimalHopfABCSSetMap ≫
          minimalHopfABCTargetSSetIsoFinThree.hom := by simp
    _ = minimalHopfABCPreimageSSetIsoFinNine.hom ≫
        (minimalHopfABCPreimageSSetIsoFinNine.inv ≫
          minimalHopfABCSSetMap) ≫
            minimalHopfABCTargetSSetIsoFinThree.hom := by
      simp only [Category.assoc]
    _ = minimalHopfABCPreimageSSetIsoFinNine.hom ≫
        (minimalHopfABCRowSSetMap ≫
          minimalHopfABCTargetSSetIsoFinThree.inv) ≫
            minimalHopfABCTargetSSetIsoFinThree.hom := by
      rw [minimalHopfABC_reindex_sSet_square]
    _ = _ := by simp

/-- The actual common-boundary map is the reindexed boundary row map from the product model. -/
theorem minimalHopfCommonBoundary_reindex_sSet_square :
    minimalHopfCommonTorusSSetIsoFinNine.inv ≫
        minimalHopfCommonBoundarySSetMap =
      minimalHopfABCCommonBoundaryRowSSetMap ≫
        minimalHopfTargetBoundarySSetIsoFinThree.inv := by
  ext Δ x
  apply Subtype.ext
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  simp [minimalHopfCommonTorusSSetIsoFinNine,
    minimalHopfTargetBoundarySSetIsoFinThree,
    minimalHopfCommonBoundarySSetMap,
    minimalHopfABCCommonBoundaryRowSSetMap,
    orderedSSetMapFacetsIso]
  change minimalHopfQuotientVertex
      (minimalHopfABCOrderEmbedding (x.1.obj i)) =
    minimalHopfABCTargetOrderEmbedding
      (minimalHopfABCRowVertex (x.1.obj i))
  exact minimalHopfABCRowVertex_reindexes_quotient (x.1.obj i)

/-- The `ABC` restriction commutes strictly with inclusion into the full finite Hopf map. -/
theorem minimalHopfABC_sSet_square :
    minimalHopfABCSSetInclSphere ≫ minimalHopfSSetMap =
      minimalHopfABCSSetMap ≫ minimalHopfABCTargetSSetInclTarget := by
  ext Δ x
  rfl

/-- The restriction of the `ABC` map to the common torus is the actual target-boundary map. -/
theorem minimalHopfABCBoundary_sSet_square :
    minimalHopfCommonBoundarySSetInclABC ≫ minimalHopfABCSSetMap =
      minimalHopfCommonBoundarySSetMap ≫
        minimalHopfTargetBoundarySSetInclABC := by
  ext Δ x
  rfl

theorem minimalHopfABC_reindex_realization_square :
    SSet.toTop.map minimalHopfABCPreimageSSetIsoFinNine.inv ≫
        SSet.toTop.map minimalHopfABCSSetMap =
      SSet.toTop.map minimalHopfABCRowSSetMap ≫
        SSet.toTop.map minimalHopfABCTargetSSetIsoFinThree.inv := by
  rw [← (SSet.toTop).map_comp, minimalHopfABC_reindex_sSet_square,
    (SSet.toTop).map_comp]

theorem minimalHopfABC_reindex_realization_square_hom :
    SSet.toTop.map minimalHopfABCSSetMap ≫
        SSet.toTop.map minimalHopfABCTargetSSetIsoFinThree.hom =
      SSet.toTop.map minimalHopfABCPreimageSSetIsoFinNine.hom ≫
        SSet.toTop.map minimalHopfABCRowSSetMap := by
  rw [← (SSet.toTop).map_comp, minimalHopfABC_reindex_sSet_square_hom,
    (SSet.toTop).map_comp]

theorem minimalHopfCommonBoundary_reindex_realization_square :
    SSet.toTop.map minimalHopfCommonTorusSSetIsoFinNine.inv ≫
        SSet.toTop.map minimalHopfCommonBoundarySSetMap =
      SSet.toTop.map minimalHopfABCCommonBoundaryRowSSetMap ≫
        SSet.toTop.map minimalHopfTargetBoundarySSetIsoFinThree.inv := by
  rw [← (SSet.toTop).map_comp,
    minimalHopfCommonBoundary_reindex_sSet_square,
    (SSet.toTop).map_comp]

theorem minimalHopfABC_realization_square :
    SSet.toTop.map minimalHopfABCSSetInclSphere ≫
        minimalHopfRealizationMap =
      SSet.toTop.map minimalHopfABCSSetMap ≫
        SSet.toTop.map minimalHopfABCTargetSSetInclTarget := by
  rw [minimalHopfRealizationMap, ← (SSet.toTop).map_comp,
    minimalHopfABC_sSet_square, (SSet.toTop).map_comp]

theorem minimalHopfABCBoundary_realization_square :
    SSet.toTop.map minimalHopfCommonBoundarySSetInclABC ≫
        SSet.toTop.map minimalHopfABCSSetMap =
      SSet.toTop.map minimalHopfCommonBoundarySSetMap ≫
        SSet.toTop.map minimalHopfTargetBoundarySSetInclABC := by
  rw [← (SSet.toTop).map_comp, minimalHopfABCBoundary_sSet_square,
    (SSet.toTop).map_comp]

/-! ## Exact product-projection coordinates -/

/-- The reindexed `ABC` realization in the already-certified product coordinates. -/
noncomputable def minimalHopfABCFinNineRealizationHomeomorphDiskTwoProdSphereOne :
    SSet.toTop.obj (orderedSSet minimalHopfABCPreimageFinNineFacets) ≃ₜ
      TopCat.disk.{0} 2 × SphereSpace 1 :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfABCPreimageFinNineFacets).trans
    (minimalHopfABCSolidTorusCarrierHomeomorphProduct.trans
      (Homeomorph.prodCongr triangleThreeCarrierHomeomorphDiskTwo
        triangleBoundaryThreeCarrierHomeomorphSphereOne))

/-- The actual target face in exact metric disk coordinates. -/
noncomputable def minimalHopfABCTargetRealizationHomeomorphDiskTwo :
    SSet.toTop.obj (orderedSSet minimalHopfABCTargetFacets) ≃ₜ
      TopCat.disk.{0} 2 :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso minimalHopfABCTargetSSetIsoFinThree)).trans
    triangleThreeRealizationHomeomorphDiskTwo

/-- First projection from the exact product solid-torus coordinates. -/
def minimalHopfDiskTwoProdSphereOneFst :
    TopCat.of (TopCat.disk.{0} 2 × SphereSpace 1) ⟶
      TopCat.of (TopCat.disk.{0} 2) :=
  TopCat.ofHom ContinuousMap.fst

/-- On the reindexed complexes, the finite Hopf map is first projection in exact
`D² × S¹ → D²` coordinates. -/
theorem minimalHopfABCRowRealization_projection_disk :
    SSet.toTop.map minimalHopfABCRowSSetMap ≫
        (TopCat.isoOfHomeo triangleThreeRealizationHomeomorphDiskTwo).hom =
      (TopCat.isoOfHomeo
          minimalHopfABCFinNineRealizationHomeomorphDiskTwoProdSphereOne).hom ≫
        minimalHopfDiskTwoProdSphereOneFst := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  have hprojection := ConcreteCategory.congr_hom
    minimalHopfABCRowRealization_projection x
  change orderedRealizationToFacetFamilyCarrier triangleThreeFacets
      (SSet.toTop.map minimalHopfABCRowSSetMap x) =
    minimalHopfABCSolidTorusCarrierProjection
      (orderedRealizationToFacetFamilyCarrier
        minimalHopfABCPreimageFinNineFacets x) at hprojection
  change triangleThreeRealizationHomeomorphDiskTwo
      (SSet.toTop.map minimalHopfABCRowSSetMap x) =
    (minimalHopfABCFinNineRealizationHomeomorphDiskTwoProdSphereOne x).1
  calc
    _ = triangleThreeCarrierHomeomorphDiskTwo
        (orderedRealizationToFacetFamilyCarrier triangleThreeFacets
          (SSet.toTop.map minimalHopfABCRowSSetMap x)) := by
      rw [triangleThreeCarrierHomeomorphDiskTwo, Homeomorph.trans_apply]
      exact congrArg triangleThreeRealizationHomeomorphDiskTwo
        ((orderedRealizationHomeomorphFacetFamilyCarrier triangleThreeFacets
          |>.symm_apply_apply
            (SSet.toTop.map minimalHopfABCRowSSetMap x)).symm)
    _ = triangleThreeCarrierHomeomorphDiskTwo
        (minimalHopfABCSolidTorusCarrierProjection
          (orderedRealizationToFacetFamilyCarrier
            minimalHopfABCPreimageFinNineFacets x)) :=
      congrArg triangleThreeCarrierHomeomorphDiskTwo
        hprojection
    _ = _ := by
      rfl

/-- On the actual finite Hopf vertex types, the `ABC` restriction is exactly first projection
under the certified solid-torus and target-disk homeomorphisms. -/
theorem minimalHopfABCRealization_projection_disk :
    SSet.toTop.map minimalHopfABCSSetMap ≫
        (TopCat.isoOfHomeo
          minimalHopfABCTargetRealizationHomeomorphDiskTwo).hom =
      (TopCat.isoOfHomeo
          minimalHopfABCPreimageRealizationHomeomorphDiskTwoProdSphereOne).hom ≫
        minimalHopfDiskTwoProdSphereOneFst := by
  change
    (SSet.toTop.map minimalHopfABCSSetMap ≫
        SSet.toTop.map minimalHopfABCTargetSSetIsoFinThree.hom) ≫
      (TopCat.isoOfHomeo triangleThreeRealizationHomeomorphDiskTwo).hom =
    (SSet.toTop.map minimalHopfABCPreimageSSetIsoFinNine.hom ≫
        (TopCat.isoOfHomeo
          minimalHopfABCFinNineRealizationHomeomorphDiskTwoProdSphereOne).hom) ≫
      minimalHopfDiskTwoProdSphereOneFst
  rw [minimalHopfABC_reindex_realization_square_hom]
  simp only [Category.assoc, minimalHopfABCRowRealization_projection_disk]

end Submission.ComplexProjectivePlaneTriangulation
