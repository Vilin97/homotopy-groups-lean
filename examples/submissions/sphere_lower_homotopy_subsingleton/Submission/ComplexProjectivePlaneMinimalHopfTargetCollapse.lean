/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfTriangulation
import Submission.FiniteOrderedComplexCarrierCollapse

/-!
# Relative collapse onto the finite Hopf target

Remove the all-interior four-simplex from the nine-vertex projective-plane triangulation.  The
remaining 35-facet complex admits an explicit sequence of 120 elementary collapses onto the
four-triangle target two-sphere.  This is the finite relative-collapse certificate needed to
compare the target cofiber with a four-sphere.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped unitInterval Topology Topology.Homotopy

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The unique displayed projective-plane facet supported on the five vertices complementary
to the finite Hopf target. -/
def minimalHopfProjectivePlaneInteriorFacet : Finset Vertex :=
  {0, 1, 2, 3, 4}

/-- The projective-plane triangulation with the all-interior four-simplex removed. -/
def minimalHopfProjectivePlanePuncturedFacets : Finset (Finset Vertex) :=
  facets.erase minimalHopfProjectivePlaneInteriorFacet

/-- A presentation of the four-triangle target produced by the collapse evaluator.  Its eight
lower-dimensional entries are redundant faces of the four terminal triangles. -/
def minimalHopfTargetCollapsePresentation : Finset (Finset Vertex) :=
  {{5}, {6}, {7}, {8}, {5, 7}, {5, 8}, {6, 8}, {7, 8},
    {5, 6, 7}, {5, 6, 8}, {5, 7, 8}, {6, 7, 8}}

/-- A complete elementary-collapse certificate from the punctured projective-plane complex to
the four-triangle target presentation. -/
def minimalHopfProjectivePlaneTargetCollapseMoves :
    List (ElementaryCollapseMoveData Vertex) :=
  [ ⟨{0, 1, 2, 3}, 8⟩,
    ⟨{0, 1, 2, 4}, 8⟩,
    ⟨{0, 1, 3, 8}, 7⟩,
    ⟨{0, 1, 3, 7}, 6⟩,
    ⟨{0, 3, 6, 7}, 8⟩,
    ⟨{0, 2, 3, 8}, 6⟩,
    ⟨{0, 2, 6, 8}, 7⟩,
    ⟨{0, 2, 4, 8}, 7⟩,
    ⟨{2, 4, 7, 8}, 6⟩,
    ⟨{1, 2, 4, 8}, 6⟩,
    ⟨{1, 2, 4, 6}, 7⟩,
    ⟨{1, 3, 6, 7}, 4⟩,
    ⟨{3, 4, 6, 7}, 8⟩,
    ⟨{0, 1, 3, 4}, 6⟩,
    ⟨{1, 2, 3, 4}, 7⟩,
    ⟨{0, 1, 4, 6}, 5⟩,
    ⟨{0, 1, 4, 5}, 8⟩,
    ⟨{1, 4, 5, 6}, 8⟩,
    ⟨{0, 1, 5, 6}, 7⟩,
    ⟨{0, 1, 5, 7}, 8⟩,
    ⟨{0, 4, 5, 8}, 7⟩,
    ⟨{0, 2, 4, 7}, 5⟩,
    ⟨{0, 2, 5, 7}, 6⟩,
    ⟨{1, 2, 6, 7}, 5⟩,
    ⟨{1, 2, 5, 6}, 8⟩,
    ⟨{0, 2, 3, 6}, 5⟩,
    ⟨{0, 3, 4, 6}, 5⟩,
    ⟨{0, 2, 3, 4}, 5⟩,
    ⟨{2, 3, 4, 5}, 7⟩,
    ⟨{1, 2, 3, 7}, 5⟩,
    ⟨{1, 2, 3, 5}, 8⟩,
    ⟨{1, 3, 5, 7}, 8⟩,
    ⟨{2, 3, 5, 6}, 8⟩,
    ⟨{3, 4, 5, 6}, 8⟩,
    ⟨{3, 4, 5, 7}, 8⟩,
    ⟨{0, 1, 2}, 8⟩,
    ⟨{0, 1, 4}, 8⟩,
    ⟨{0, 1, 5}, 8⟩,
    ⟨{1, 4, 5}, 8⟩,
    ⟨{0, 1, 8}, 7⟩,
    ⟨{0, 2, 8}, 7⟩,
    ⟨{0, 4, 8}, 7⟩,
    ⟨{0, 5, 8}, 7⟩,
    ⟨{0, 4, 7}, 5⟩,
    ⟨{0, 1, 7}, 6⟩,
    ⟨{0, 2, 7}, 6⟩,
    ⟨{0, 5, 7}, 6⟩,
    ⟨{0, 2, 6}, 5⟩,
    ⟨{0, 2, 4}, 5⟩,
    ⟨{0, 4, 6}, 5⟩,
    ⟨{0, 6, 7}, 8⟩,
    ⟨{2, 7, 8}, 6⟩,
    ⟨{1, 2, 6}, 8⟩,
    ⟨{1, 4, 8}, 6⟩,
    ⟨{4, 5, 6}, 8⟩,
    ⟨{1, 6, 8}, 5⟩,
    ⟨{1, 5, 6}, 7⟩,
    ⟨{1, 6, 7}, 4⟩,
    ⟨{2, 4, 5}, 7⟩,
    ⟨{4, 5, 7}, 8⟩,
    ⟨{1, 2, 4}, 7⟩,
    ⟨{1, 2, 7}, 5⟩,
    ⟨{1, 5, 7}, 8⟩,
    ⟨{1, 2, 5}, 8⟩,
    ⟨{2, 4, 8}, 6⟩,
    ⟨{2, 4, 6}, 7⟩,
    ⟨{2, 6, 7}, 5⟩,
    ⟨{2, 5, 6}, 8⟩,
    ⟨{4, 6, 7}, 8⟩,
    ⟨{0, 1, 3}, 6⟩,
    ⟨{0, 5, 6}, 3⟩,
    ⟨{0, 2, 3}, 5⟩,
    ⟨{0, 3, 4}, 5⟩,
    ⟨{0, 3, 6}, 8⟩,
    ⟨{3, 5, 6}, 8⟩,
    ⟨{2, 5, 8}, 3⟩,
    ⟨{2, 3, 6}, 8⟩,
    ⟨{3, 4, 5}, 8⟩,
    ⟨{4, 6, 8}, 3⟩,
    ⟨{1, 3, 6}, 4⟩,
    ⟨{0, 3, 7}, 8⟩,
    ⟨{3, 4, 8}, 7⟩,
    ⟨{1, 3, 4}, 7⟩,
    ⟨{1, 3, 7}, 8⟩,
    ⟨{1, 2, 3}, 8⟩,
    ⟨{1, 3, 5}, 8⟩,
    ⟨{3, 5, 8}, 7⟩,
    ⟨{2, 3, 5}, 7⟩,
    ⟨{2, 3, 4}, 7⟩,
    ⟨{3, 6, 7}, 8⟩,
    ⟨{0, 1}, 6⟩,
    ⟨{0, 6}, 8⟩,
    ⟨{0, 7}, 8⟩,
    ⟨{0, 8}, 3⟩,
    ⟨{0, 3}, 5⟩,
    ⟨{0, 2}, 5⟩,
    ⟨{0, 4}, 5⟩,
    ⟨{1, 3}, 8⟩,
    ⟨{1, 2}, 8⟩,
    ⟨{2, 6}, 8⟩,
    ⟨{2, 8}, 3⟩,
    ⟨{1, 5}, 8⟩,
    ⟨{1, 8}, 7⟩,
    ⟨{4, 5}, 8⟩,
    ⟨{4, 8}, 7⟩,
    ⟨{1, 7}, 4⟩,
    ⟨{1, 4}, 6⟩,
    ⟨{2, 3}, 7⟩,
    ⟨{2, 4}, 7⟩,
    ⟨{2, 5}, 7⟩,
    ⟨{3, 5}, 7⟩,
    ⟨{4, 7}, 3⟩,
    ⟨{3, 7}, 8⟩,
    ⟨{3, 4}, 6⟩,
    ⟨{3, 6}, 8⟩,
    ⟨{0}, 5⟩,
    ⟨{1}, 6⟩,
    ⟨{4}, 6⟩,
    ⟨{2}, 7⟩,
    ⟨{3}, 8⟩ ]

/-- The relative collapse uses 120 elementary moves. -/
theorem minimalHopfProjectivePlaneTargetCollapseMoves_length :
    minimalHopfProjectivePlaneTargetCollapseMoves.length = 120 := by
  decide

/-- Each free face contains an interior vertex, so the collapse leaves the target carrier
pointwise fixed. -/
theorem minimalHopfProjectivePlaneTargetCollapseMoves_relative
    (move : ElementaryCollapseMoveData Vertex)
    (hmove : move ∈ minimalHopfProjectivePlaneTargetCollapseMoves) :
    ¬move.freeFace ⊆ minimalHopfTargetVertices := by
  exact (by decide : ∀ m ∈ minimalHopfProjectivePlaneTargetCollapseMoves,
    ¬m.freeFace ⊆ minimalHopfTargetVertices) move hmove

/-- Every move is valid at the facet family produced by its predecessors. -/
theorem minimalHopfProjectivePlaneTargetCollapseMoves_valid :
    IsValidElementaryCollapseMoveSequence
      minimalHopfProjectivePlanePuncturedFacets
      minimalHopfProjectivePlaneTargetCollapseMoves := by
  decide

/-- The checked endpoint is the displayed target presentation. -/
theorem minimalHopfProjectivePlaneTargetCollapseMoves_result :
    applyElementaryCollapseMoves
        minimalHopfProjectivePlanePuncturedFacets
        minimalHopfProjectivePlaneTargetCollapseMoves =
      minimalHopfTargetCollapsePresentation := by
  decide

/-- The terminal presentation and the original four-facet presentation define the same target
subcomplex, in the forward direction. -/
theorem minimalHopfTargetCollapsePresentation_le_target :
    FacetFamilyLE minimalHopfTargetCollapsePresentation
      minimalHopfTargetFacets := by
  intro facet hfacet
  exact (by decide : ∀ f : {f // f ∈ minimalHopfTargetCollapsePresentation},
    IsFace minimalHopfTargetFacets f.1) ⟨facet, hfacet⟩

/-- The terminal presentation and the original four-facet presentation define the same target
subcomplex, in the reverse direction. -/
theorem minimalHopfTargetFacets_le_collapsePresentation :
    FacetFamilyLE minimalHopfTargetFacets
      minimalHopfTargetCollapsePresentation := by
  intro facet hfacet
  exact (by decide : ∀ f : {f // f ∈ minimalHopfTargetFacets},
    IsFace minimalHopfTargetCollapsePresentation f.1) ⟨facet, hfacet⟩

/-- The evaluator's terminal carrier is canonically homeomorphic to the maintained target
carrier. -/
def minimalHopfTargetCollapsePresentationCarrierHomeomorph :
    facetFamilyCarrier minimalHopfTargetCollapsePresentation ≃ₜ
      facetFamilyCarrier minimalHopfTargetFacets where
  toFun := facetFamilyCarrierMapOfFacetFamilyLE
    minimalHopfTargetCollapsePresentation_le_target
  invFun := facetFamilyCarrierMapOfFacetFamilyLE
    minimalHopfTargetFacets_le_collapsePresentation
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_facetFamilyCarrierMapOfFacetFamilyLE
    minimalHopfTargetCollapsePresentation_le_target
  continuous_invFun := continuous_facetFamilyCarrierMapOfFacetFamilyLE
    minimalHopfTargetFacets_le_collapsePresentation

/-- The computed endpoint is a facet-family refinement of the maintained target. -/
theorem minimalHopfProjectivePlaneTargetCollapseResult_le_target :
    FacetFamilyLE
      (applyElementaryCollapseMoves
        minimalHopfProjectivePlanePuncturedFacets
        minimalHopfProjectivePlaneTargetCollapseMoves)
      minimalHopfTargetFacets := by
  rw [minimalHopfProjectivePlaneTargetCollapseMoves_result]
  exact minimalHopfTargetCollapsePresentation_le_target

/-- The maintained target is a facet-family refinement of the computed endpoint. -/
theorem minimalHopfTargetFacets_le_projectivePlaneTargetCollapseResult :
    FacetFamilyLE minimalHopfTargetFacets
      (applyElementaryCollapseMoves
        minimalHopfProjectivePlanePuncturedFacets
        minimalHopfProjectivePlaneTargetCollapseMoves) := by
  rw [minimalHopfProjectivePlaneTargetCollapseMoves_result]
  exact minimalHopfTargetFacets_le_collapsePresentation

/-- The computed endpoint carrier is canonically homeomorphic to the maintained target carrier,
without transporting its type across the evaluator equality. -/
def minimalHopfProjectivePlaneTargetCollapseResultCarrierHomeomorph :
    facetFamilyCarrier
        (applyElementaryCollapseMoves
          minimalHopfProjectivePlanePuncturedFacets
          minimalHopfProjectivePlaneTargetCollapseMoves) ≃ₜ
      facetFamilyCarrier minimalHopfTargetFacets where
  toFun := facetFamilyCarrierMapOfFacetFamilyLE
    minimalHopfProjectivePlaneTargetCollapseResult_le_target
  invFun := facetFamilyCarrierMapOfFacetFamilyLE
    minimalHopfTargetFacets_le_projectivePlaneTargetCollapseResult
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_facetFamilyCarrierMapOfFacetFamilyLE
    minimalHopfProjectivePlaneTargetCollapseResult_le_target
  continuous_invFun := continuous_facetFamilyCarrierMapOfFacetFamilyLE
    minimalHopfTargetFacets_le_projectivePlaneTargetCollapseResult

/-- The punctured nine-vertex projective-plane carrier is homotopy equivalent to the finite
Hopf target carrier. -/
def minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget :
    ContinuousMap.HomotopyEquiv
      (facetFamilyCarrier minimalHopfProjectivePlanePuncturedFacets)
      (facetFamilyCarrier minimalHopfTargetFacets) :=
  (elementaryCollapseMoveSequenceCarrierHomotopyEquiv
      minimalHopfProjectivePlanePuncturedFacets
      minimalHopfProjectivePlaneTargetCollapseMoves
      minimalHopfProjectivePlaneTargetCollapseMoves_valid).trans
    minimalHopfProjectivePlaneTargetCollapseResultCarrierHomeomorph.toHomotopyEquiv

/-- The four-triangle target is a subcomplex of the punctured projective-plane complex. -/
theorem minimalHopfTargetFacets_le_projectivePlanePunctured :
    FacetFamilyLE minimalHopfTargetFacets
      minimalHopfProjectivePlanePuncturedFacets := by
  intro facet hfacet
  exact (by decide : ∀ f : {f // f ∈ minimalHopfTargetFacets},
    IsFace minimalHopfProjectivePlanePuncturedFacets f.1) ⟨facet, hfacet⟩

/-- The literal affine-carrier inclusion of the target into the punctured complex. -/
def minimalHopfTargetCarrierInclPunctured :
    C(facetFamilyCarrier minimalHopfTargetFacets,
      facetFamilyCarrier minimalHopfProjectivePlanePuncturedFacets) :=
  ⟨facetFamilyCarrierMapOfFacetFamilyLE
      minimalHopfTargetFacets_le_projectivePlanePunctured,
    continuous_facetFamilyCarrierMapOfFacetFamilyLE
      minimalHopfTargetFacets_le_projectivePlanePunctured⟩

/-- The inverse in the collapse equivalence is exactly the literal target inclusion. -/
theorem minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget_invFun :
    minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget.invFun =
      minimalHopfTargetCarrierInclPunctured := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact elementaryCollapseMoveSequenceCarrierHomotopyEquiv_invFun_val
    minimalHopfProjectivePlanePuncturedFacets
    minimalHopfProjectivePlaneTargetCollapseMoves
    minimalHopfProjectivePlaneTargetCollapseMoves_valid
    (minimalHopfProjectivePlaneTargetCollapseResultCarrierHomeomorph.symm x)

/-- The relative collapse retraction is strictly the identity on the included target. -/
theorem minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget_toFun_incl
    (x : facetFamilyCarrier minimalHopfTargetFacets) :
    minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget.toFun
        (minimalHopfTargetCarrierInclPunctured x) = x := by
  apply Subtype.ext
  exact elementaryCollapseMoveSequenceCarrierHomotopyEquiv_toFun_val_eq_of_support
    minimalHopfProjectivePlanePuncturedFacets
    minimalHopfProjectivePlaneTargetCollapseMoves
    minimalHopfProjectivePlaneTargetCollapseMoves_valid
    minimalHopfTargetVertices
    minimalHopfProjectivePlaneTargetCollapseMoves_relative
    (minimalHopfTargetCarrierInclPunctured x)
    (by
      intro v hv
      obtain ⟨facet, hfacet, hsupport⟩ :=
        (mem_facetFamilyCarrier_iff minimalHopfTargetFacets x.1).mp x.2
      apply hsupport v
      intro hvfacet
      apply hv
      exact (by decide : ∀ f : {f // f ∈ minimalHopfTargetFacets},
        f.1 ⊆ minimalHopfTargetVertices) ⟨facet, hfacet⟩ hvfacet)

/-- As continuous maps, collapse after target inclusion is strictly the identity. -/
theorem minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget_toFun_comp_incl :
    minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget.toFun.comp
        minimalHopfTargetCarrierInclPunctured =
      ContinuousMap.id (facetFamilyCarrier minimalHopfTargetFacets) := by
  apply ContinuousMap.ext
  exact minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget_toFun_incl

/-- The literal target inclusion into the punctured projective-plane carrier is a homotopy
equivalence. -/
def minimalHopfTargetCarrierInclPuncturedHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (facetFamilyCarrier minimalHopfTargetFacets)
      (facetFamilyCarrier minimalHopfProjectivePlanePuncturedFacets) :=
  minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget.symm

/-- The forward map of the target-inclusion homotopy equivalence is the literal inclusion. -/
theorem minimalHopfTargetCarrierInclPuncturedHomotopyEquiv_toFun :
    minimalHopfTargetCarrierInclPuncturedHomotopyEquiv.toFun =
      minimalHopfTargetCarrierInclPunctured :=
  minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget_invFun

/-- The simplicial target inclusion into the punctured projective-plane complex. -/
def minimalHopfTargetSSetInclPunctured :
    orderedSSet minimalHopfTargetFacets ⟶
      orderedSSet minimalHopfProjectivePlanePuncturedFacets :=
  orderedSSetHomOfFacetFamilyLE
    minimalHopfTargetFacets_le_projectivePlanePunctured

/-- The realized target inclusion into the punctured complex is a homotopy equivalence. -/
def minimalHopfTargetRealizationInclPuncturedHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (orderedSSet minimalHopfTargetFacets))
      (SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlanePuncturedFacets)) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfTargetFacets).toHomotopyEquiv.trans
    (minimalHopfTargetCarrierInclPuncturedHomotopyEquiv.trans
      (orderedRealizationHomeomorphFacetFamilyCarrier
        minimalHopfProjectivePlanePuncturedFacets).symm.toHomotopyEquiv)

/-- The forward map of the realized relative-collapse equivalence is the literal simplicial
target inclusion. -/
theorem minimalHopfTargetRealizationInclPuncturedHomotopyEquiv_toFun :
    minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.toFun =
      (SSet.toTop.map minimalHopfTargetSSetInclPunctured).hom := by
  apply ContinuousMap.ext
  intro x
  change (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfProjectivePlanePuncturedFacets).symm
        (minimalHopfTargetCarrierInclPuncturedHomotopyEquiv.toFun
          (orderedRealizationHomeomorphFacetFamilyCarrier
            minimalHopfTargetFacets x)) =
      SSet.toTop.map minimalHopfTargetSSetInclPunctured x
  rw [minimalHopfTargetCarrierInclPuncturedHomotopyEquiv_toFun]
  apply (orderedRealizationHomeomorphFacetFamilyCarrier
    minimalHopfProjectivePlanePuncturedFacets).injective
  rw [Homeomorph.apply_symm_apply]
  simpa [minimalHopfTargetSSetInclPunctured,
    ConcreteCategory.comp_apply, facetFamilyCarrierHomOfFacetFamilyLE,
    minimalHopfTargetCarrierInclPunctured,
    orderedRealizationHomeomorphFacetFamilyCarrier] using
    (ConcreteCategory.congr_hom
      (orderedRealizationToFacetFamilyCarrier_naturality
        minimalHopfTargetFacets_le_projectivePlanePunctured) x).symm

/-- The realized collapse retraction is strictly the identity after the realized target
inclusion. -/
theorem minimalHopfTargetRealizationInclPuncturedHomotopyEquiv_invFun_toFun
    (x : SSet.toTop.obj (orderedSSet minimalHopfTargetFacets)) :
    minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun
        (minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.toFun x) = x := by
  change (orderedRealizationHomeomorphFacetFamilyCarrier minimalHopfTargetFacets).symm
      (minimalHopfTargetCarrierInclPuncturedHomotopyEquiv.invFun
        ((orderedRealizationHomeomorphFacetFamilyCarrier
          minimalHopfProjectivePlanePuncturedFacets)
          ((orderedRealizationHomeomorphFacetFamilyCarrier
            minimalHopfProjectivePlanePuncturedFacets).symm
            (minimalHopfTargetCarrierInclPuncturedHomotopyEquiv.toFun
              (orderedRealizationHomeomorphFacetFamilyCarrier
                minimalHopfTargetFacets x))))) = x
  rw [Homeomorph.apply_symm_apply]
  change (orderedRealizationHomeomorphFacetFamilyCarrier minimalHopfTargetFacets).symm
      (minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget.toFun
        (minimalHopfTargetCarrierInclPunctured
          (orderedRealizationHomeomorphFacetFamilyCarrier
            minimalHopfTargetFacets x))) = x
  rw [minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget_toFun_incl]
  exact Homeomorph.symm_apply_apply _ x

/-- As continuous maps, the realized collapse retraction followed by target inclusion is the
identity. -/
theorem minimalHopfTargetRealizationInclPuncturedHomotopyEquiv_invFun_comp_incl :
    minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun.comp
        (SSet.toTop.map minimalHopfTargetSSetInclPunctured).hom =
      ContinuousMap.id (SSet.toTop.obj (orderedSSet minimalHopfTargetFacets)) := by
  rw [← minimalHopfTargetRealizationInclPuncturedHomotopyEquiv_toFun]
  apply ContinuousMap.ext
  exact minimalHopfTargetRealizationInclPuncturedHomotopyEquiv_invFun_toFun

/-- The explicit strong deformation from target-inclusion-after-collapse back to the identity on
the punctured affine carrier. -/
noncomputable def minimalHopfProjectivePlanePuncturedCarrierDeformation :
    ContinuousMap.Homotopy
      (minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget.invFun.comp
        minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget.toFun)
      (ContinuousMap.id
        (facetFamilyCarrier minimalHopfProjectivePlanePuncturedFacets)) := by
  let e := elementaryCollapseMoveSequenceCarrierHomotopyEquiv
    minimalHopfProjectivePlanePuncturedFacets
    minimalHopfProjectivePlaneTargetCollapseMoves
    minimalHopfProjectivePlaneTargetCollapseMoves_valid
  let h := minimalHopfProjectivePlaneTargetCollapseResultCarrierHomeomorph
  let H := elementaryCollapseMoveSequenceCarrierDeformation
    minimalHopfProjectivePlanePuncturedFacets
    minimalHopfProjectivePlaneTargetCollapseMoves
    minimalHopfProjectivePlaneTargetCollapseMoves_valid
  have hstart : e.invFun.comp e.toFun =
      minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget.invFun.comp
        minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget.toFun := by
    apply ContinuousMap.ext
    intro x
    change e.invFun (e.toFun x) = e.invFun (h.symm (h (e.toFun x)))
    rw [Homeomorph.symm_apply_apply]
  exact H.cast hstart rfl

/-- The punctured-carrier collapse retraction is constant throughout its explicit deformation. -/
theorem minimalHopfProjectivePlanePuncturedCarrierDeformation_toFun
    (t : I)
    (x : facetFamilyCarrier minimalHopfProjectivePlanePuncturedFacets) :
    minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget.toFun
        (minimalHopfProjectivePlanePuncturedCarrierDeformation (t, x)) =
      minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget.toFun x := by
  let e := elementaryCollapseMoveSequenceCarrierHomotopyEquiv
    minimalHopfProjectivePlanePuncturedFacets
    minimalHopfProjectivePlaneTargetCollapseMoves
    minimalHopfProjectivePlaneTargetCollapseMoves_valid
  let h := minimalHopfProjectivePlaneTargetCollapseResultCarrierHomeomorph
  let H := elementaryCollapseMoveSequenceCarrierDeformation
    minimalHopfProjectivePlanePuncturedFacets
    minimalHopfProjectivePlaneTargetCollapseMoves
    minimalHopfProjectivePlaneTargetCollapseMoves_valid
  apply Subtype.ext
  change (h (e.toFun (H (t, x)))).1 = (h (e.toFun x)).1
  exact congrArg (fun y ↦ (h y).1)
    (elementaryCollapseMoveSequenceCarrierDeformation_toFun
      minimalHopfProjectivePlanePuncturedFacets
      minimalHopfProjectivePlaneTargetCollapseMoves
      minimalHopfProjectivePlaneTargetCollapseMoves_valid t x)

/-- The relative collapse transported to geometric realization as an explicit strong
deformation. -/
noncomputable def minimalHopfProjectivePlanePuncturedRealizationDeformation :
    ContinuousMap.Homotopy
      (minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.toFun.comp
        minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun)
      (ContinuousMap.id
        (SSet.toTop.obj
          (orderedSSet minimalHopfProjectivePlanePuncturedFacets))) where
  toFun p :=
    (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfProjectivePlanePuncturedFacets).symm
        (minimalHopfProjectivePlanePuncturedCarrierDeformation
          (p.1, orderedRealizationHomeomorphFacetFamilyCarrier
            minimalHopfProjectivePlanePuncturedFacets p.2))
  continuous_toFun :=
    (orderedRealizationHomeomorphFacetFamilyCarrier
        minimalHopfProjectivePlanePuncturedFacets).symm.continuous.comp
      (minimalHopfProjectivePlanePuncturedCarrierDeformation.continuous.comp
        (continuous_fst.prodMk
          ((orderedRealizationHomeomorphFacetFamilyCarrier
            minimalHopfProjectivePlanePuncturedFacets).continuous.comp
              continuous_snd)))
  map_zero_left x := by
    let hp := orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfProjectivePlanePuncturedFacets
    let ht := orderedRealizationHomeomorphFacetFamilyCarrier minimalHopfTargetFacets
    let e := minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget
    change hp.symm
      (minimalHopfProjectivePlanePuncturedCarrierDeformation (0, hp x)) = _
    rw [ContinuousMap.Homotopy.apply_zero]
    change hp.symm (e.invFun (e.toFun (hp x))) =
      hp.symm (e.invFun (ht (ht.symm (e.toFun (hp x)))))
    rw [Homeomorph.apply_symm_apply]
  map_one_left x := by
    change (orderedRealizationHomeomorphFacetFamilyCarrier
        minimalHopfProjectivePlanePuncturedFacets).symm
      (minimalHopfProjectivePlanePuncturedCarrierDeformation
        (1, orderedRealizationHomeomorphFacetFamilyCarrier
          minimalHopfProjectivePlanePuncturedFacets x)) = x
    rw [ContinuousMap.Homotopy.apply_one]
    exact (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfProjectivePlanePuncturedFacets).symm_apply_apply x

/-- The realized collapse retraction stays constant throughout the explicit punctured-complex
deformation. -/
theorem minimalHopfProjectivePlanePuncturedRealizationDeformation_invFun
    (t : I)
    (x : SSet.toTop.obj
      (orderedSSet minimalHopfProjectivePlanePuncturedFacets)) :
    minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun
        (minimalHopfProjectivePlanePuncturedRealizationDeformation (t, x)) =
      minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun x := by
  let hp := orderedRealizationHomeomorphFacetFamilyCarrier
    minimalHopfProjectivePlanePuncturedFacets
  let ht := orderedRealizationHomeomorphFacetFamilyCarrier minimalHopfTargetFacets
  let e := minimalHopfProjectivePlanePuncturedCarrierHomotopyEquivTarget
  change ht.symm
      (e.toFun (hp (hp.symm
        (minimalHopfProjectivePlanePuncturedCarrierDeformation (t, hp x))))) =
    ht.symm (e.toFun (hp x))
  rw [Homeomorph.apply_symm_apply,
    minimalHopfProjectivePlanePuncturedCarrierDeformation_toFun]

/-! ## Reattaching the all-interior four-simplex -/

/-- The single-facet presentation of the all-interior four-simplex. -/
def minimalHopfProjectivePlaneInteriorSimplexFacets :
    Finset (Finset Vertex) :=
  {minimalHopfProjectivePlaneInteriorFacet}

/-- The five-tetrahedron boundary of the all-interior four-simplex. -/
def minimalHopfProjectivePlaneInteriorBoundaryFacets :
    Finset (Finset Vertex) :=
  simplexBoundaryFacets minimalHopfProjectivePlaneInteriorFacet

theorem minimalHopfProjectivePlaneInteriorBoundaryFacets_le_punctured :
    FacetFamilyLE minimalHopfProjectivePlaneInteriorBoundaryFacets
      minimalHopfProjectivePlanePuncturedFacets := by
  intro facet hfacet
  exact (by decide : ∀ f :
      {f // f ∈ minimalHopfProjectivePlaneInteriorBoundaryFacets},
    IsFace minimalHopfProjectivePlanePuncturedFacets f.1) ⟨facet, hfacet⟩

theorem minimalHopfProjectivePlaneInteriorBoundaryFacets_le_simplex :
    FacetFamilyLE minimalHopfProjectivePlaneInteriorBoundaryFacets
      minimalHopfProjectivePlaneInteriorSimplexFacets := by
  intro facet hfacet
  exact (by decide : ∀ f :
      {f // f ∈ minimalHopfProjectivePlaneInteriorBoundaryFacets},
    IsFace minimalHopfProjectivePlaneInteriorSimplexFacets f.1) ⟨facet, hfacet⟩

theorem minimalHopfProjectivePlanePuncturedSimplex_pairwise_intersections :
    ∀ puncturedFacet ∈ minimalHopfProjectivePlanePuncturedFacets,
      ∀ simplexFacet ∈ minimalHopfProjectivePlaneInteriorSimplexFacets,
        IsFace minimalHopfProjectivePlaneInteriorBoundaryFacets
          (puncturedFacet ∩ simplexFacet) := by
  intro puncturedFacet hpunctured simplexFacet hsimplex
  exact (by decide :
    ∀ left : {f // f ∈ minimalHopfProjectivePlanePuncturedFacets},
      ∀ right : {f // f ∈ minimalHopfProjectivePlaneInteriorSimplexFacets},
        IsFace minimalHopfProjectivePlaneInteriorBoundaryFacets
          (left.1 ∩ right.1)) ⟨puncturedFacet, hpunctured⟩
            ⟨simplexFacet, hsimplex⟩

theorem minimalHopfProjectivePlanePuncturedSimplexSubcomplex_inf :
    orderedSubcomplex minimalHopfProjectivePlanePuncturedFacets ⊓
        orderedSubcomplex minimalHopfProjectivePlaneInteriorSimplexFacets =
      orderedSubcomplex minimalHopfProjectivePlaneInteriorBoundaryFacets :=
  orderedSubcomplex_inf_eq_of_pairwise_intersections
    minimalHopfProjectivePlaneInteriorBoundaryFacets
    minimalHopfProjectivePlanePuncturedFacets
    minimalHopfProjectivePlaneInteriorSimplexFacets
    minimalHopfProjectivePlanePuncturedSimplex_pairwise_intersections
    minimalHopfProjectivePlaneInteriorBoundaryFacets_le_punctured
    minimalHopfProjectivePlaneInteriorBoundaryFacets_le_simplex

theorem minimalHopfProjectivePlanePuncturedSimplexFacets_union :
    minimalHopfProjectivePlanePuncturedFacets ∪
        minimalHopfProjectivePlaneInteriorSimplexFacets = facets := by
  decide

theorem minimalHopfProjectivePlanePuncturedSimplexSubcomplex_sup :
    orderedSubcomplex minimalHopfProjectivePlanePuncturedFacets ⊔
        orderedSubcomplex minimalHopfProjectivePlaneInteriorSimplexFacets =
      orderedSubcomplex facets := by
  rw [← orderedSubcomplex_union,
    minimalHopfProjectivePlanePuncturedSimplexFacets_union]

theorem minimalHopfProjectivePlanePuncturedSimplexBicartSq :
    Lattice.BicartSq
      (orderedSubcomplex minimalHopfProjectivePlaneInteriorBoundaryFacets)
      (orderedSubcomplex minimalHopfProjectivePlanePuncturedFacets)
      (orderedSubcomplex minimalHopfProjectivePlaneInteriorSimplexFacets)
      (orderedSubcomplex facets) where
  sup_eq := minimalHopfProjectivePlanePuncturedSimplexSubcomplex_sup
  inf_eq := minimalHopfProjectivePlanePuncturedSimplexSubcomplex_inf

theorem minimalHopfProjectivePlanePuncturedFacets_le_projectivePlane :
    FacetFamilyLE minimalHopfProjectivePlanePuncturedFacets facets := by
  intro facet hfacet
  exact (by decide :
    ∀ f : {f // f ∈ minimalHopfProjectivePlanePuncturedFacets},
      IsFace facets f.1) ⟨facet, hfacet⟩

theorem minimalHopfProjectivePlaneInteriorSimplexFacets_le_projectivePlane :
    FacetFamilyLE minimalHopfProjectivePlaneInteriorSimplexFacets facets := by
  intro facet hfacet
  exact (by decide : ∀ f :
      {f // f ∈ minimalHopfProjectivePlaneInteriorSimplexFacets},
    IsFace facets f.1) ⟨facet, hfacet⟩

def minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured :
    orderedSSet minimalHopfProjectivePlaneInteriorBoundaryFacets ⟶
      orderedSSet minimalHopfProjectivePlanePuncturedFacets :=
  orderedSSetHomOfFacetFamilyLE
    minimalHopfProjectivePlaneInteriorBoundaryFacets_le_punctured

def minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex :
    orderedSSet minimalHopfProjectivePlaneInteriorBoundaryFacets ⟶
      orderedSSet minimalHopfProjectivePlaneInteriorSimplexFacets :=
  orderedSSetHomOfFacetFamilyLE
    minimalHopfProjectivePlaneInteriorBoundaryFacets_le_simplex

def minimalHopfProjectivePlanePuncturedSSetIncl :
    orderedSSet minimalHopfProjectivePlanePuncturedFacets ⟶
      projectivePlaneSSet :=
  orderedSSetHomOfFacetFamilyLE
    minimalHopfProjectivePlanePuncturedFacets_le_projectivePlane

def minimalHopfProjectivePlaneInteriorSimplexSSetIncl :
    orderedSSet minimalHopfProjectivePlaneInteriorSimplexFacets ⟶
      projectivePlaneSSet :=
  orderedSSetHomOfFacetFamilyLE
    minimalHopfProjectivePlaneInteriorSimplexFacets_le_projectivePlane

/-- The punctured complex and the all-interior four-simplex reconstruct the nine-vertex
projective-plane simplicial set by gluing along the simplex boundary. -/
theorem minimalHopfProjectivePlanePuncturedSimplex_isPushout :
    IsPushout minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured
      minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex
      minimalHopfProjectivePlanePuncturedSSetIncl
      minimalHopfProjectivePlaneInteriorSimplexSSetIncl := by
  exact SSet.Subcomplex.BicartSq.isPushout
    minimalHopfProjectivePlanePuncturedSimplexBicartSq

/-- Geometric realization preserves the punctured-complex/four-simplex pushout. -/
theorem minimalHopfProjectivePlanePuncturedSimplexRealization_isPushout :
    IsPushout
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured)
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex)
      (SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl)
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorSimplexSSetIncl) :=
  minimalHopfProjectivePlanePuncturedSimplex_isPushout.map SSet.toTop

/-- The attaching map of the remaining four-simplex, transported from the punctured complex to
the finite Hopf target by the relative collapse retraction. -/
noncomputable def minimalHopfProjectivePlaneTargetAttachingMap :
    SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlaneInteriorBoundaryFacets) ⟶
      SSet.toTop.obj (orderedSSet minimalHopfTargetFacets) :=
  TopCat.ofHom
    (minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun.comp
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured).hom)

/-- Re-including the collapsed attaching map is homotopic to the original boundary inclusion
into the punctured projective plane. -/
theorem minimalHopfProjectivePlaneTargetAttachingMap_incl_homotopic :
    ((SSet.toTop.map minimalHopfTargetSSetInclPunctured).hom.comp
        minimalHopfProjectivePlaneTargetAttachingMap.hom).Homotopic
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured).hom := by
  rw [← minimalHopfTargetRealizationInclPuncturedHomotopyEquiv_toFun]
  change ((minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.toFun.comp
      minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun).comp
        (SSet.toTop.map
          minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured).hom).Homotopic _
  simpa using
    minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.right_inv.comp
      (ContinuousMap.Homotopic.refl
        (SSet.toTop.map
          minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured).hom)

end Submission.ComplexProjectivePlaneTriangulation
