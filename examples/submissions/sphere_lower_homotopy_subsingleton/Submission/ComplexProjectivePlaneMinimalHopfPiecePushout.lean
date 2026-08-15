/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfABCPieceMap

/-!
# Pushout gluing of the two finite Hopf pieces

The finite Hopf source is the union of its `ABC` and complementary pieces along their common
torus.  Its target is likewise the union of the face `ABC` and the complementary cone disk along
their triangular boundary.  This file upgrades those finite union/intersection calculations to
actual pushout squares of simplicial sets and, by realization, topological spaces.

Consequently the full finite Hopf map is uniquely determined by the two already-certified piece
maps.  This is a gluing statement about the finite map; it does not identify the complementary
source with a solid torus or the global realized map with the quadratic Hopf map.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## A finite intersection criterion -/

/-- If every left/right facet intersection is a face of `common`, and every common facet is a
face on both sides, then the generated ordered subcomplexes intersect exactly in `common`. -/
theorem orderedSubcomplex_inf_eq_of_pairwise_intersections
    {V : Type} [LinearOrder V]
    (common left right : Finset (Finset V))
    (hinter : ∀ leftFacet ∈ left, ∀ rightFacet ∈ right,
      IsFace common (leftFacet ∩ rightFacet))
    (hleft : FacetFamilyLE common left)
    (hright : FacetFamilyLE common right) :
    orderedSubcomplex left ⊓ orderedSubcomplex right =
      orderedSubcomplex common := by
  ext Δ x
  constructor
  · intro hx
    change x ∈ (orderedSubcomplex left).obj Δ ∧
      x ∈ (orderedSubcomplex right).obj Δ at hx
    rcases hx with ⟨⟨leftFacet, hleftFacet, hxleft⟩,
      ⟨rightFacet, hrightFacet, hxright⟩⟩
    obtain ⟨commonFacet, hcommonFacet, hsubset⟩ :=
      hinter leftFacet hleftFacet rightFacet hrightFacet
    exact ⟨commonFacet, hcommonFacet, fun i ↦
      hsubset (Finset.mem_inter.mpr ⟨hxleft i, hxright i⟩)⟩
  · intro hx
    change x ∈ (orderedSubcomplex left).obj Δ ∧
      x ∈ (orderedSubcomplex right).obj Δ
    exact ⟨orderedSubcomplex_mono_of_facetFamilyLE hleft Δ hx,
      orderedSubcomplex_mono_of_facetFamilyLE hright Δ hx⟩

/-! ## Source pushout -/

theorem minimalHopfSourcePiece_pairwise_intersections :
    ∀ leftFacet ∈ minimalHopfABCPreimageFacets,
      ∀ rightFacet ∈ minimalHopfComplementPreimageFacets,
        IsFace minimalHopfCommonTorusFacets (leftFacet ∩ rightFacet) := by
  intro leftFacet hleftFacet rightFacet hrightFacet
  exact (by decide :
    ∀ left : ↥minimalHopfABCPreimageFacets,
      ∀ right : ↥minimalHopfComplementPreimageFacets,
        IsFace minimalHopfCommonTorusFacets (left.1 ∩ right.1))
    ⟨leftFacet, hleftFacet⟩ ⟨rightFacet, hrightFacet⟩

theorem minimalHopfSourcePieceSubcomplex_inf :
    orderedSubcomplex minimalHopfABCPreimageFacets ⊓
        orderedSubcomplex minimalHopfComplementPreimageFacets =
      orderedSubcomplex minimalHopfCommonTorusFacets :=
  orderedSubcomplex_inf_eq_of_pairwise_intersections
    minimalHopfCommonTorusFacets minimalHopfABCPreimageFacets
    minimalHopfComplementPreimageFacets
    minimalHopfSourcePiece_pairwise_intersections
    minimalHopfCommonTorusFacets_le_ABC
    minimalHopfCommonTorusFacets_le_complement

theorem minimalHopfSourcePieceSubcomplex_sup :
    orderedSubcomplex minimalHopfABCPreimageFacets ⊔
        orderedSubcomplex minimalHopfComplementPreimageFacets =
      orderedSubcomplex minimalHopfSphereFacets := by
  rw [← orderedSubcomplex_union, minimalHopfPreimageFacets_union]

theorem minimalHopfSourcePieceBicartSq :
    Lattice.BicartSq
      (orderedSubcomplex minimalHopfCommonTorusFacets)
      (orderedSubcomplex minimalHopfABCPreimageFacets)
      (orderedSubcomplex minimalHopfComplementPreimageFacets)
      (orderedSubcomplex minimalHopfSphereFacets) where
  sup_eq := minimalHopfSourcePieceSubcomplex_sup
  inf_eq := minimalHopfSourcePieceSubcomplex_inf

/-- The common torus, the two source pieces, and the full finite Hopf sphere form a pushout. -/
theorem minimalHopfSourcePiece_isPushout :
    IsPushout minimalHopfCommonBoundarySSetInclABC
      minimalHopfCommonBoundarySSetInclComplement
      minimalHopfABCSSetInclSphere minimalHopfComplementSSetInclSphere := by
  exact SSet.Subcomplex.BicartSq.isPushout minimalHopfSourcePieceBicartSq

/-- Geometric realization preserves the source-piece pushout. -/
theorem minimalHopfSourcePieceRealization_isPushout :
    IsPushout
      (SSet.toTop.map minimalHopfCommonBoundarySSetInclABC)
      (SSet.toTop.map minimalHopfCommonBoundarySSetInclComplement)
      (SSet.toTop.map minimalHopfABCSSetInclSphere)
      (SSet.toTop.map minimalHopfComplementSSetInclSphere) :=
  minimalHopfSourcePiece_isPushout.map SSet.toTop

/-! ## Target pushout -/

theorem minimalHopfTargetBoundaryFacets_le_complement :
    FacetFamilyLE minimalHopfTargetBoundaryFacets
      minimalHopfComplementTargetFacets := by
  intro facet hfacet
  exact (by decide : ∀ σ : ↥minimalHopfTargetBoundaryFacets,
    IsFace minimalHopfComplementTargetFacets σ.1) ⟨facet, hfacet⟩

def minimalHopfTargetBoundarySSetInclComplementLE :
    orderedSSet minimalHopfTargetBoundaryFacets ⟶
      orderedSSet minimalHopfComplementTargetFacets :=
  orderedSSetHomOfFacetFamilyLE minimalHopfTargetBoundaryFacets_le_complement

theorem minimalHopfTargetBoundarySSetInclComplement_eq_LE :
    minimalHopfTargetBoundarySSetInclComplement =
      minimalHopfTargetBoundarySSetInclComplementLE := by
  ext Δ x
  rfl

theorem minimalHopfTargetPieceFacets_union :
    minimalHopfABCTargetFacets ∪ minimalHopfComplementTargetFacets =
      minimalHopfTargetFacets := by
  decide

theorem minimalHopfTargetPiece_pairwise_intersections :
    ∀ leftFacet ∈ minimalHopfABCTargetFacets,
      ∀ rightFacet ∈ minimalHopfComplementTargetFacets,
        IsFace minimalHopfTargetBoundaryFacets (leftFacet ∩ rightFacet) := by
  intro leftFacet hleftFacet rightFacet hrightFacet
  exact (by decide :
    ∀ left : ↥minimalHopfABCTargetFacets,
      ∀ right : ↥minimalHopfComplementTargetFacets,
        IsFace minimalHopfTargetBoundaryFacets (left.1 ∩ right.1))
    ⟨leftFacet, hleftFacet⟩ ⟨rightFacet, hrightFacet⟩

theorem minimalHopfTargetPieceSubcomplex_inf :
    orderedSubcomplex minimalHopfABCTargetFacets ⊓
        orderedSubcomplex minimalHopfComplementTargetFacets =
      orderedSubcomplex minimalHopfTargetBoundaryFacets :=
  orderedSubcomplex_inf_eq_of_pairwise_intersections
    minimalHopfTargetBoundaryFacets minimalHopfABCTargetFacets
    minimalHopfComplementTargetFacets
    minimalHopfTargetPiece_pairwise_intersections
    minimalHopfTargetBoundaryFacets_le_ABC
    minimalHopfTargetBoundaryFacets_le_complement

theorem minimalHopfTargetPieceSubcomplex_sup :
    orderedSubcomplex minimalHopfABCTargetFacets ⊔
        orderedSubcomplex minimalHopfComplementTargetFacets =
      orderedSubcomplex minimalHopfTargetFacets := by
  rw [← orderedSubcomplex_union, minimalHopfTargetPieceFacets_union]

theorem minimalHopfTargetPieceBicartSq :
    Lattice.BicartSq
      (orderedSubcomplex minimalHopfTargetBoundaryFacets)
      (orderedSubcomplex minimalHopfABCTargetFacets)
      (orderedSubcomplex minimalHopfComplementTargetFacets)
      (orderedSubcomplex minimalHopfTargetFacets) where
  sup_eq := minimalHopfTargetPieceSubcomplex_sup
  inf_eq := minimalHopfTargetPieceSubcomplex_inf

/-- The triangular boundary, the two target disks, and the finite target sphere form a
pushout. -/
theorem minimalHopfTargetPiece_isPushout :
    IsPushout minimalHopfTargetBoundarySSetInclABC
      minimalHopfTargetBoundarySSetInclComplement
      minimalHopfABCTargetSSetInclTarget
      minimalHopfComplementTargetSSetInclTarget := by
  rw [minimalHopfTargetBoundarySSetInclComplement_eq_LE]
  exact SSet.Subcomplex.BicartSq.isPushout minimalHopfTargetPieceBicartSq

/-- Geometric realization preserves the target-disk pushout. -/
theorem minimalHopfTargetPieceRealization_isPushout :
    IsPushout
      (SSet.toTop.map minimalHopfTargetBoundarySSetInclABC)
      (SSet.toTop.map minimalHopfTargetBoundarySSetInclComplement)
      (SSet.toTop.map minimalHopfABCTargetSSetInclTarget)
      (SSet.toTop.map minimalHopfComplementTargetSSetInclTarget) :=
  minimalHopfTargetPiece_isPushout.map SSet.toTop

/-! ## Uniqueness of the glued finite Hopf map -/

/-- A simplicial map out of the finite source sphere is the finite Hopf map as soon as it has the
certified restrictions on both source pieces. -/
theorem minimalHopfSSetMap_eq_of_piece_restrictions
    (f : orderedSSet minimalHopfSphereFacets ⟶
      orderedSSet minimalHopfTargetFacets)
    (hABC : minimalHopfABCSSetInclSphere ≫ f =
      minimalHopfABCSSetMap ≫ minimalHopfABCTargetSSetInclTarget)
    (hComplement : minimalHopfComplementSSetInclSphere ≫ f =
      minimalHopfComplementSSetMap ≫
        minimalHopfComplementTargetSSetInclTarget) :
    f = minimalHopfSSetMap := by
  apply minimalHopfSourcePiece_isPushout.hom_ext
  · rw [hABC, minimalHopfABC_sSet_square]
  · rw [hComplement, minimalHopfComplement_sSet_square]

/-- The analogous uniqueness statement after geometric realization. -/
theorem minimalHopfRealizationMap_eq_of_piece_restrictions
    (f : SSet.toTop.obj (orderedSSet minimalHopfSphereFacets) ⟶
      SSet.toTop.obj (orderedSSet minimalHopfTargetFacets))
    (hABC : SSet.toTop.map minimalHopfABCSSetInclSphere ≫ f =
      SSet.toTop.map minimalHopfABCSSetMap ≫
        SSet.toTop.map minimalHopfABCTargetSSetInclTarget)
    (hComplement :
      SSet.toTop.map minimalHopfComplementSSetInclSphere ≫ f =
        SSet.toTop.map minimalHopfComplementSSetMap ≫
          SSet.toTop.map minimalHopfComplementTargetSSetInclTarget) :
    f = minimalHopfRealizationMap := by
  apply minimalHopfSourcePieceRealization_isPushout.hom_ext
  · rw [hABC, minimalHopfABC_realization_square]
  · rw [hComplement, minimalHopfComplement_realization_square]

end Submission.ComplexProjectivePlaneTriangulation
