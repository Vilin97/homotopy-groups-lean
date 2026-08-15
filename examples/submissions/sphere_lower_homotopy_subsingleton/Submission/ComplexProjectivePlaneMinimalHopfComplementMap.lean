/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfBoundaryProjection
import Submission.FiniteOrderedComplexConeRealization
import Submission.Topology.DiskBoundaryCone

/-!
# The complementary finite Hopf map over a target disk

The complementary twenty-seven-tetrahedron piece maps to the three target triangles containing
`D`.  Those triangles form the cone from `D` over the boundary of `ABC`, hence realize as the
exact disk `D²`.  This file packages the restricted simplicial map and proves that both its
ambient square and its common-boundary square commute strictly.  It also identifies the target
boundary inclusion with the standard inclusion `∂D² → D²` in explicit disk coordinates.

No solid-torus recognition theorem for the source complement is used here.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## The complementary target disk -/

/-- The triangular boundary of the target face `ABC`. -/
def minimalHopfTargetBoundaryFacets : Finset (Finset Vertex) :=
  {{5, 6}, {5, 7}, {6, 7}}

/-- The three target triangles containing `D`. -/
def minimalHopfComplementTargetFacets : Finset (Finset Vertex) :=
  {{5, 6, 8}, {5, 7, 8}, {6, 7, 8}}

/-- The vertices supporting the target face `ABC`. -/
def minimalHopfABCTargetVertices : Finset Vertex := {5, 6, 7}

theorem minimalHopfTargetBoundaryFacets_eq_simplexBoundary :
    minimalHopfTargetBoundaryFacets =
      simplexBoundaryFacets minimalHopfABCTargetVertices := by
  decide

theorem minimalHopfABCTargetVertices_card :
    minimalHopfABCTargetVertices.card = 2 + 1 := by
  decide

/-- The complementary target disk is literally the cone from `D` over the target boundary. -/
theorem minimalHopfComplementTargetFacets_isCone :
    minimalHopfTargetBoundaryFacets.image (fun facet ↦ insert 8 facet) =
      minimalHopfComplementTargetFacets := by
  decide

theorem minimalHopfTargetBoundary_apex_not_mem :
    ∀ facet ∈ minimalHopfTargetBoundaryFacets, 8 ∉ facet := by
  decide

theorem minimalHopfTargetBoundary_nonempty :
    ∃ facet ∈ minimalHopfTargetBoundaryFacets, facet.Nonempty := by
  decide

noncomputable def minimalHopfTargetBoundarySSetIsoBoundaryTwo :
    orderedSSet minimalHopfTargetBoundaryFacets ≅
      (SSet.boundary 2 : SSet) :=
  SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex
        minimalHopfTargetBoundaryFacets_eq_simplexBoundary) ≪≫
    simplexBoundarySSetIso 2 minimalHopfABCTargetVertices
      minimalHopfABCTargetVertices_card

/-- The target boundary realizes as the exact metric circle. -/
noncomputable def minimalHopfTargetBoundaryRealizationHomeomorphSphereOne :
    SSet.toTop.obj (orderedSSet minimalHopfTargetBoundaryFacets) ≃ₜ
      SphereSpace 1 :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso minimalHopfTargetBoundarySSetIsoBoundaryTwo)).trans
    (boundaryRealizationHomeomorphSphere 1)

/-- The same target boundary in the exact boundary coordinates of `D²`. -/
noncomputable def minimalHopfTargetBoundaryRealizationHomeomorphDiskBoundaryTwo :
    SSet.toTop.obj (orderedSSet minimalHopfTargetBoundaryFacets) ≃ₜ
      TopCat.diskBoundary.{0} 2 :=
  minimalHopfTargetBoundaryRealizationHomeomorphSphereOne.trans
    (diskBoundaryHomeoSph 1).symm

def minimalHopfComplementTargetConeSSetIso :
    orderedSSet
        (minimalHopfTargetBoundaryFacets.image
          (fun facet ↦ insert 8 facet)) ≅
      orderedSSet minimalHopfComplementTargetFacets :=
  SSet.Subcomplex.eqToIso
    (congrArg orderedSubcomplex minimalHopfComplementTargetFacets_isCone)

/-- Inclusion of the target boundary into its complementary cone disk. -/
def minimalHopfTargetBoundarySSetInclComplement :
    orderedSSet minimalHopfTargetBoundaryFacets ⟶
      orderedSSet minimalHopfComplementTargetFacets :=
  orderedConeBaseIncl minimalHopfTargetBoundaryFacets 8 ≫
    minimalHopfComplementTargetConeSSetIso.hom

noncomputable def
    minimalHopfComplementTargetRealizationHomeomorphTopologicalCone :
    SSet.toTop.obj (orderedSSet minimalHopfComplementTargetFacets) ≃ₜ
      topologicalCone
        (SSet.toTop.obj (orderedSSet minimalHopfTargetBoundaryFacets)) :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso minimalHopfComplementTargetConeSSetIso).symm).trans
    (conedOrderedRealizationHomeomorphTopologicalCone
      minimalHopfTargetBoundaryFacets 8
      minimalHopfTargetBoundary_apex_not_mem
      minimalHopfTargetBoundary_nonempty)

theorem minimalHopfComplementTargetRealizationHomeomorphTopologicalCone_base
    (x : SSet.toTop.obj (orderedSSet minimalHopfTargetBoundaryFacets)) :
    minimalHopfComplementTargetRealizationHomeomorphTopologicalCone
        (SSet.toTop.map minimalHopfTargetBoundarySSetInclComplement x) =
      topologicalConeBaseIncl
        (SSet.toTop.obj (orderedSSet minimalHopfTargetBoundaryFacets)) x := by
  let q := minimalHopfComplementTargetConeSSetIso
  have hcancel :
      SSet.toTop.map minimalHopfTargetBoundarySSetInclComplement ≫
          (SSet.toTop.mapIso q).inv =
        SSet.toTop.map
          (orderedConeBaseIncl minimalHopfTargetBoundaryFacets 8) := by
    rw [minimalHopfTargetBoundarySSetInclComplement, Functor.map_comp]
    change
      (SSet.toTop.map
          (orderedConeBaseIncl minimalHopfTargetBoundaryFacets 8) ≫
        SSet.toTop.map q.hom) ≫ SSet.toTop.map q.inv =
      SSet.toTop.map
        (orderedConeBaseIncl minimalHopfTargetBoundaryFacets 8)
    rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      Iso.hom_inv_id, Category.comp_id]
  change conedOrderedRealizationHomeomorphTopologicalCone
      minimalHopfTargetBoundaryFacets 8
      minimalHopfTargetBoundary_apex_not_mem
      minimalHopfTargetBoundary_nonempty
      ((TopCat.homeoOfIso (SSet.toTop.mapIso q).symm)
        (SSet.toTop.map minimalHopfTargetBoundarySSetInclComplement x)) = _
  rw [show
      (TopCat.homeoOfIso (SSet.toTop.mapIso q).symm)
          (SSet.toTop.map minimalHopfTargetBoundarySSetInclComplement x) =
        SSet.toTop.map
          (orderedConeBaseIncl minimalHopfTargetBoundaryFacets 8) x by
    have h := ConcreteCategory.congr_hom hcancel x
    change (SSet.toTop.mapIso q).inv
        (SSet.toTop.map minimalHopfTargetBoundarySSetInclComplement x) =
      SSet.toTop.map
        (orderedConeBaseIncl minimalHopfTargetBoundaryFacets 8) x
    simpa only [ConcreteCategory.comp_apply] using h]
  exact conedOrderedRealizationHomeomorphTopologicalCone_base
    minimalHopfTargetBoundaryFacets 8
    minimalHopfTargetBoundary_apex_not_mem
    minimalHopfTargetBoundary_nonempty x

/-- The three-triangle complementary target is the exact metric disk `D²`. -/
noncomputable def minimalHopfComplementTargetRealizationHomeomorphDiskTwo :
    SSet.toTop.obj (orderedSSet minimalHopfComplementTargetFacets) ≃ₜ
      TopCat.disk.{0} 2 :=
  minimalHopfComplementTargetRealizationHomeomorphTopologicalCone.trans
    ((TopCat.homeoOfIso (topologicalConeIso
      (TopCat.isoOfHomeo
        minimalHopfTargetBoundaryRealizationHomeomorphDiskBoundaryTwo))).trans
      (diskBoundarySuccConeHomeomorphDisk (n := 1)))

/-- In the chosen disk coordinates, the finite cone-base inclusion is the standard boundary
inclusion `∂D² → D²`. -/
theorem minimalHopfComplementTargetRealizationHomeomorphDiskTwo_base
    (x : SSet.toTop.obj (orderedSSet minimalHopfTargetBoundaryFacets)) :
    minimalHopfComplementTargetRealizationHomeomorphDiskTwo
        (SSet.toTop.map minimalHopfTargetBoundarySSetInclComplement x) =
      TopCat.diskBoundaryIncl 2
        (minimalHopfTargetBoundaryRealizationHomeomorphDiskBoundaryTwo x) := by
  let e := TopCat.isoOfHomeo
    minimalHopfTargetBoundaryRealizationHomeomorphDiskBoundaryTwo
  rw [minimalHopfComplementTargetRealizationHomeomorphDiskTwo,
    Homeomorph.trans_apply, Homeomorph.trans_apply,
    minimalHopfComplementTargetRealizationHomeomorphTopologicalCone_base]
  have hcone := ConcreteCategory.congr_hom
    (topologicalConeBaseIncl_iso_hom e) x
  have hdisk := ConcreteCategory.congr_hom
    (diskBoundarySuccConeBaseIncl_isoDisk (n := 1)) (e.hom x)
  rw [show
      (TopCat.homeoOfIso (topologicalConeIso e))
          (topologicalConeBaseIncl
            (SSet.toTop.obj (orderedSSet minimalHopfTargetBoundaryFacets)) x) =
        topologicalConeBaseIncl (TopCat.diskBoundary 2) (e.hom x) by
    change (topologicalConeIso e).hom
        (topologicalConeBaseIncl
          (SSet.toTop.obj (orderedSSet minimalHopfTargetBoundaryFacets)) x) =
      topologicalConeBaseIncl (TopCat.diskBoundary 2) (e.hom x)
    simpa only [ConcreteCategory.comp_apply] using hcone]
  change (diskBoundarySuccConeIsoDisk (n := 1)).hom
      (topologicalConeBaseIncl (TopCat.diskBoundary 2) (e.hom x)) =
    TopCat.diskBoundaryIncl 2 (e.hom x)
  simpa only [ConcreteCategory.comp_apply, Nat.reduceAdd] using hdisk

/-! ## Restriction of the finite Hopf map -/

theorem minimalHopfComplementFacetFamilyMapsTo :
    FacetFamilyMapsTo minimalHopfQuotientVertex
      minimalHopfComplementPreimageFacets minimalHopfComplementTargetFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfComplementPreimageFacets,
    IsFace minimalHopfComplementTargetFacets
      (σ.1.image minimalHopfQuotientVertex)) ⟨facet, hfacet⟩

theorem minimalHopfCommonTorusFacetFamilyMapsToTargetBoundary :
    FacetFamilyMapsTo minimalHopfQuotientVertex
      minimalHopfCommonTorusFacets minimalHopfTargetBoundaryFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfCommonTorusFacets,
    IsFace minimalHopfTargetBoundaryFacets
      (σ.1.image minimalHopfQuotientVertex)) ⟨facet, hfacet⟩

theorem minimalHopfComplementPreimageFacets_le_sphere :
    FacetFamilyLE minimalHopfComplementPreimageFacets minimalHopfSphereFacets := by
  intro facet hfacet
  exact ⟨facet, Finset.mem_sdiff.mp hfacet |>.1, Finset.Subset.rfl⟩

theorem minimalHopfComplementTargetFacets_le_target :
    FacetFamilyLE minimalHopfComplementTargetFacets minimalHopfTargetFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfComplementTargetFacets,
    IsFace minimalHopfTargetFacets σ.1) ⟨facet, hfacet⟩

theorem minimalHopfCommonTorusFacets_le_complement :
    FacetFamilyLE minimalHopfCommonTorusFacets
      minimalHopfComplementPreimageFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfCommonTorusFacets,
    IsFace minimalHopfComplementPreimageFacets σ.1) ⟨facet, hfacet⟩

def minimalHopfComplementSSetMap :
    orderedSSet minimalHopfComplementPreimageFacets ⟶
      orderedSSet minimalHopfComplementTargetFacets :=
  orderedSSetMapOfMonotone minimalHopfQuotientVertex
    minimalHopfComplementFacetFamilyMapsTo

def minimalHopfCommonBoundarySSetMap :
    orderedSSet minimalHopfCommonTorusFacets ⟶
      orderedSSet minimalHopfTargetBoundaryFacets :=
  orderedSSetMapOfMonotone minimalHopfQuotientVertex
    minimalHopfCommonTorusFacetFamilyMapsToTargetBoundary

def minimalHopfComplementSSetInclSphere :
    orderedSSet minimalHopfComplementPreimageFacets ⟶
      orderedSSet minimalHopfSphereFacets :=
  orderedSSetHomOfFacetFamilyLE minimalHopfComplementPreimageFacets_le_sphere

def minimalHopfComplementTargetSSetInclTarget :
    orderedSSet minimalHopfComplementTargetFacets ⟶
      orderedSSet minimalHopfTargetFacets :=
  orderedSSetHomOfFacetFamilyLE minimalHopfComplementTargetFacets_le_target

def minimalHopfCommonBoundarySSetInclComplement :
    orderedSSet minimalHopfCommonTorusFacets ⟶
      orderedSSet minimalHopfComplementPreimageFacets :=
  orderedSSetHomOfFacetFamilyLE minimalHopfCommonTorusFacets_le_complement

/-- The complementary map is the strict restriction of the full finite Hopf map. -/
theorem minimalHopfComplement_sSet_square :
    minimalHopfComplementSSetInclSphere ≫ minimalHopfSSetMap =
      minimalHopfComplementSSetMap ≫
        minimalHopfComplementTargetSSetInclTarget := by
  ext Δ x
  rfl

/-- On the common torus, the complementary map restricts to the same target-boundary map. -/
theorem minimalHopfComplementBoundary_sSet_square :
    minimalHopfCommonBoundarySSetInclComplement ≫
        minimalHopfComplementSSetMap =
      minimalHopfCommonBoundarySSetMap ≫
        minimalHopfTargetBoundarySSetInclComplement := by
  ext Δ x
  rfl

theorem minimalHopfComplement_realization_square :
    SSet.toTop.map minimalHopfComplementSSetInclSphere ≫
        minimalHopfRealizationMap =
      SSet.toTop.map minimalHopfComplementSSetMap ≫
        SSet.toTop.map minimalHopfComplementTargetSSetInclTarget := by
  rw [minimalHopfRealizationMap, ← (SSet.toTop).map_comp,
    minimalHopfComplement_sSet_square, (SSet.toTop).map_comp]

theorem minimalHopfComplementBoundary_realization_square :
    SSet.toTop.map minimalHopfCommonBoundarySSetInclComplement ≫
        SSet.toTop.map minimalHopfComplementSSetMap =
      SSet.toTop.map minimalHopfCommonBoundarySSetMap ≫
        SSet.toTop.map minimalHopfTargetBoundarySSetInclComplement := by
  rw [← (SSet.toTop).map_comp, minimalHopfComplementBoundary_sSet_square,
    (SSet.toTop).map_comp]

/-- The complementary finite Hopf map expressed in exact disk coordinates. -/
noncomputable def minimalHopfComplementDiskMap :
    SSet.toTop.obj (orderedSSet minimalHopfComplementPreimageFacets) ⟶
      TopCat.of (TopCat.disk.{0} 2) :=
  SSet.toTop.map minimalHopfComplementSSetMap ≫
    (TopCat.isoOfHomeo
      minimalHopfComplementTargetRealizationHomeomorphDiskTwo).hom

/-- The common-boundary restriction expressed in the exact boundary coordinates of `D²`. -/
noncomputable def minimalHopfCommonBoundaryDiskBoundaryMap :
    SSet.toTop.obj (orderedSSet minimalHopfCommonTorusFacets) ⟶
      TopCat.of (TopCat.diskBoundary.{0} 2) :=
  SSet.toTop.map minimalHopfCommonBoundarySSetMap ≫
    (TopCat.isoOfHomeo
      minimalHopfTargetBoundaryRealizationHomeomorphDiskBoundaryTwo).hom

/-- The restricted finite Hopf map is a strict map of pairs from the complementary source piece
and its common torus to `(D², ∂D²)`. -/
theorem minimalHopfComplementDiskMap_boundary :
    SSet.toTop.map minimalHopfCommonBoundarySSetInclComplement ≫
        minimalHopfComplementDiskMap =
      minimalHopfCommonBoundaryDiskBoundaryMap ≫
        TopCat.diskBoundaryIncl 2 := by
  have htarget :
      SSet.toTop.map minimalHopfTargetBoundarySSetInclComplement ≫
          (TopCat.isoOfHomeo
            minimalHopfComplementTargetRealizationHomeomorphDiskTwo).hom =
        (TopCat.isoOfHomeo
            minimalHopfTargetBoundaryRealizationHomeomorphDiskBoundaryTwo).hom ≫
          TopCat.diskBoundaryIncl 2 := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact minimalHopfComplementTargetRealizationHomeomorphDiskTwo_base x
  rw [minimalHopfComplementDiskMap,
    minimalHopfCommonBoundaryDiskBoundaryMap, ← Category.assoc,
    minimalHopfComplementBoundary_realization_square]
  simp only [Category.assoc, htarget]

/-- The realized complementary map is the affine barycentric pushforward along the finite
quotient. -/
theorem minimalHopfComplementRealization_carrier_naturality :
    SSet.toTop.map minimalHopfComplementSSetMap ≫
        orderedRealizationToFacetFamilyCarrier
          minimalHopfComplementTargetFacets =
      orderedRealizationToFacetFamilyCarrier
          minimalHopfComplementPreimageFacets ≫
        facetFamilyCarrierHomOfMonotone minimalHopfQuotientVertex
          minimalHopfComplementFacetFamilyMapsTo :=
  orderedRealizationToFacetFamilyCarrier_naturality_monotone
    minimalHopfQuotientVertex minimalHopfComplementFacetFamilyMapsTo

end Submission.ComplexProjectivePlaneTriangulation
