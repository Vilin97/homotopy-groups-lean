/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfBallInteriorBoundaryCollapseCertificate
import Submission.ComplexProjectivePlaneMinimalHopfAttachingComparison

/-!
# The finite Hopf attaching-domain comparison is a homotopy equivalence

The certified 321-move collapse of the punctured ambient complex onto the distinguished
simplex boundary is promoted to a homotopy equivalence whose forward map is the literal
boundary inclusion.  Reindexing that boundary by the projective-plane vertices and composing
with the inverse of the original-boundary inclusion identifies the attaching-domain comparison
with a homotopy equivalence.  Thus the collapsed attaching map is the certified finite Hopf map
up to a homotopy equivalence of its domain sphere.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped unitInterval Topology Topology.Homotopy

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## Collapse onto the distinguished ambient boundary -/

/-- The collapse certificate's maintained endpoint is the ambient interior-simplex boundary
used by the attaching comparison. -/
theorem minimalHopfBallInteriorBoundaryCollapseFacets_eq :
    minimalHopfBallInteriorBoundaryCollapseFacets =
      minimalHopfBallInteriorBoundaryFacets := by
  rfl

/-- The computed collapse endpoint carrier is canonically homeomorphic to the maintained
interior-boundary carrier. -/
def minimalHopfBallInteriorBoundaryCollapseResultCarrierHomeomorph :
    facetFamilyCarrier
        (applyElementaryCollapseMoves minimalHopfBallPuncturedFacets
          minimalHopfBallInteriorBoundaryCollapseMoves) ≃ₜ
      facetFamilyCarrier minimalHopfBallInteriorBoundaryFacets where
  toFun := facetFamilyCarrierMapOfFacetFamilyLE (by
    rw [minimalHopfBallInteriorBoundaryCollapseMoves_result,
      ← minimalHopfBallInteriorBoundaryCollapseFacets_eq]
    exact minimalHopfBallInteriorBoundaryCollapsePresentation_le_boundary)
  invFun := facetFamilyCarrierMapOfFacetFamilyLE (by
    rw [minimalHopfBallInteriorBoundaryCollapseMoves_result,
      ← minimalHopfBallInteriorBoundaryCollapseFacets_eq]
    exact minimalHopfBallInteriorBoundaryCollapseFacets_le_presentation)
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_facetFamilyCarrierMapOfFacetFamilyLE (by
    rw [minimalHopfBallInteriorBoundaryCollapseMoves_result,
      ← minimalHopfBallInteriorBoundaryCollapseFacets_eq]
    exact minimalHopfBallInteriorBoundaryCollapsePresentation_le_boundary)
  continuous_invFun := continuous_facetFamilyCarrierMapOfFacetFamilyLE (by
    rw [minimalHopfBallInteriorBoundaryCollapseMoves_result,
      ← minimalHopfBallInteriorBoundaryCollapseFacets_eq]
    exact minimalHopfBallInteriorBoundaryCollapseFacets_le_presentation)

/-- The punctured ambient carrier is homotopy equivalent to the distinguished interior
boundary carrier. -/
def minimalHopfBallPuncturedCarrierHomotopyEquivInteriorBoundary :
    ContinuousMap.HomotopyEquiv
      (facetFamilyCarrier minimalHopfBallPuncturedFacets)
      (facetFamilyCarrier minimalHopfBallInteriorBoundaryFacets) :=
  (elementaryCollapseMoveSequenceCarrierHomotopyEquiv
      minimalHopfBallPuncturedFacets
      minimalHopfBallInteriorBoundaryCollapseMoves
      minimalHopfBallInteriorBoundaryCollapseMoves_valid).trans
    minimalHopfBallInteriorBoundaryCollapseResultCarrierHomeomorph.toHomotopyEquiv

/-- The literal affine-carrier inclusion of the distinguished boundary into the punctured
ambient complex. -/
def minimalHopfBallInteriorBoundaryCarrierInclPunctured :
    C(facetFamilyCarrier minimalHopfBallInteriorBoundaryFacets,
      facetFamilyCarrier minimalHopfBallPuncturedFacets) :=
  ⟨facetFamilyCarrierMapOfFacetFamilyLE
      minimalHopfBallInteriorBoundaryFacets_le_punctured,
    continuous_facetFamilyCarrierMapOfFacetFamilyLE
      minimalHopfBallInteriorBoundaryFacets_le_punctured⟩

/-- The inverse in the collapse equivalence is the literal interior-boundary inclusion. -/
theorem minimalHopfBallPuncturedCarrierHomotopyEquivInteriorBoundary_invFun :
    minimalHopfBallPuncturedCarrierHomotopyEquivInteriorBoundary.invFun =
      minimalHopfBallInteriorBoundaryCarrierInclPunctured := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact elementaryCollapseMoveSequenceCarrierHomotopyEquiv_invFun_val
    minimalHopfBallPuncturedFacets
    minimalHopfBallInteriorBoundaryCollapseMoves
    minimalHopfBallInteriorBoundaryCollapseMoves_valid
    (minimalHopfBallInteriorBoundaryCollapseResultCarrierHomeomorph.symm x)

/-- The literal distinguished-boundary inclusion is a homotopy equivalence. -/
def minimalHopfBallInteriorBoundaryCarrierInclPuncturedHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (facetFamilyCarrier minimalHopfBallInteriorBoundaryFacets)
      (facetFamilyCarrier minimalHopfBallPuncturedFacets) :=
  minimalHopfBallPuncturedCarrierHomotopyEquivInteriorBoundary.symm

/-- The forward map of the carrier equivalence is the literal inclusion. -/
theorem minimalHopfBallInteriorBoundaryCarrierInclPuncturedHomotopyEquiv_toFun :
    minimalHopfBallInteriorBoundaryCarrierInclPuncturedHomotopyEquiv.toFun =
      minimalHopfBallInteriorBoundaryCarrierInclPunctured :=
  minimalHopfBallPuncturedCarrierHomotopyEquivInteriorBoundary_invFun

/-- The realized distinguished-boundary inclusion into the punctured ambient complex is a
homotopy equivalence. -/
def minimalHopfBallInteriorBoundaryRealizationInclPuncturedHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (orderedSSet minimalHopfBallInteriorBoundaryFacets))
      (SSet.toTop.obj (orderedSSet minimalHopfBallPuncturedFacets)) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfBallInteriorBoundaryFacets).toHomotopyEquiv.trans
    (minimalHopfBallInteriorBoundaryCarrierInclPuncturedHomotopyEquiv.trans
      (orderedRealizationHomeomorphFacetFamilyCarrier
        minimalHopfBallPuncturedFacets).symm.toHomotopyEquiv)

/-- The forward map of the realized equivalence is the literal simplicial inclusion. -/
theorem minimalHopfBallInteriorBoundaryRealizationInclPuncturedHomotopyEquiv_toFun :
    minimalHopfBallInteriorBoundaryRealizationInclPuncturedHomotopyEquiv.toFun =
      (SSet.toTop.map minimalHopfBallInteriorBoundarySSetInclPunctured).hom := by
  apply ContinuousMap.ext
  intro x
  change (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfBallPuncturedFacets).symm
        (minimalHopfBallInteriorBoundaryCarrierInclPuncturedHomotopyEquiv.toFun
          (orderedRealizationHomeomorphFacetFamilyCarrier
            minimalHopfBallInteriorBoundaryFacets x)) =
      SSet.toTop.map minimalHopfBallInteriorBoundarySSetInclPunctured x
  rw [minimalHopfBallInteriorBoundaryCarrierInclPuncturedHomotopyEquiv_toFun]
  apply (orderedRealizationHomeomorphFacetFamilyCarrier
    minimalHopfBallPuncturedFacets).injective
  rw [Homeomorph.apply_symm_apply]
  simpa [minimalHopfBallInteriorBoundarySSetInclPunctured,
    ConcreteCategory.comp_apply, facetFamilyCarrierHomOfFacetFamilyLE,
    minimalHopfBallInteriorBoundaryCarrierInclPunctured,
    orderedRealizationHomeomorphFacetFamilyCarrier] using
    (ConcreteCategory.congr_hom
      (orderedRealizationToFacetFamilyCarrier_naturality
        minimalHopfBallInteriorBoundaryFacets_le_punctured) x).symm

/-! ## Reindexing the distinguished boundary -/

/-- The vertex section maps the projective-plane interior simplex to the distinguished ambient
interior simplex. -/
theorem minimalHopfQuotientVertexSection_map_interiorFacet :
    minimalHopfProjectivePlaneInteriorFacet.map
        minimalHopfQuotientVertexSection.toEmbedding =
      minimalHopfBallInteriorFacet := by
  decide

/-- Reindexing maps the projective-plane interior boundary onto the distinguished ambient
interior boundary. -/
theorem map_minimalHopfProjectivePlaneInteriorBoundaryFacets :
    mapFacets minimalHopfQuotientVertexSection.toEmbedding
        minimalHopfProjectivePlaneInteriorBoundaryFacets =
      minimalHopfBallInteriorBoundaryFacets := by
  rw [minimalHopfProjectivePlaneInteriorBoundaryFacets,
    minimalHopfBallInteriorBoundaryFacets,
    mapFacets_simplexBoundaryFacets,
    minimalHopfQuotientVertexSection_map_interiorFacet]

/-- Reindex the projective-plane interior boundary as the distinguished ambient boundary. -/
noncomputable def minimalHopfInteriorBoundarySSetIso :
    orderedSSet minimalHopfProjectivePlaneInteriorBoundaryFacets ≅
      orderedSSet minimalHopfBallInteriorBoundaryFacets :=
  orderedSSetMapFacetsIso minimalHopfQuotientVertexSection
      minimalHopfProjectivePlaneInteriorBoundaryFacets ≪≫
    SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex
        map_minimalHopfProjectivePlaneInteriorBoundaryFacets)

/-- The reindexing isomorphism is the boundary lift used in the attaching comparison. -/
theorem minimalHopfInteriorBoundarySSetIso_hom :
    minimalHopfInteriorBoundarySSetIso.hom =
      minimalHopfInteriorBoundaryLiftSSetMap := by
  ext Δ x
  apply Subtype.ext
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  simp [minimalHopfInteriorBoundarySSetIso,
    minimalHopfInteriorBoundaryLiftSSetMap,
    orderedSSetMapFacetsIso, orderedSSetMapOfMonotone]
  rfl

/-- The realized boundary lift is a homotopy equivalence. -/
noncomputable def minimalHopfInteriorBoundaryLiftRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlaneInteriorBoundaryFacets))
      (SSet.toTop.obj (orderedSSet minimalHopfBallInteriorBoundaryFacets)) :=
  (TopCat.homeoOfIso
    (SSet.toTop.mapIso minimalHopfInteriorBoundarySSetIso)).toHomotopyEquiv

/-- The forward map of the realized reindexing equivalence is the original boundary lift. -/
theorem minimalHopfInteriorBoundaryLiftRealizationHomotopyEquiv_toFun :
    minimalHopfInteriorBoundaryLiftRealizationHomotopyEquiv.toFun =
      (SSet.toTop.map minimalHopfInteriorBoundaryLiftSSetMap).hom := by
  change (SSet.toTop.map minimalHopfInteriorBoundarySSetIso.hom).hom = _
  rw [minimalHopfInteriorBoundarySSetIso_hom]

/-! ## The attaching-domain equivalence -/

/-- The domain comparison from the collapsed projective-plane attaching sphere to the finite
Hopf domain is a homotopy equivalence. -/
noncomputable def minimalHopfAttachingDomainComparisonHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlaneInteriorBoundaryFacets))
      (SSet.toTop.obj (orderedSSet minimalHopfSphereFacets)) :=
  minimalHopfInteriorBoundaryLiftRealizationHomotopyEquiv.trans
    (minimalHopfBallInteriorBoundaryRealizationInclPuncturedHomotopyEquiv.trans
      minimalHopfSphereRealizationInclBallPuncturedHomotopyEquiv.symm)

/-- The forward map of the domain equivalence is exactly the comparison previously used in the
attaching-map homotopy. -/
theorem minimalHopfAttachingDomainComparisonHomotopyEquiv_toFun :
    minimalHopfAttachingDomainComparisonHomotopyEquiv.toFun =
      minimalHopfAttachingDomainComparison.hom := by
  apply ContinuousMap.ext
  intro x
  change minimalHopfSphereRealizationInclBallPuncturedHomotopyEquiv.invFun
      (minimalHopfBallInteriorBoundaryRealizationInclPuncturedHomotopyEquiv.toFun
        (minimalHopfInteriorBoundaryLiftRealizationHomotopyEquiv.toFun x)) =
    minimalHopfAttachingDomainComparison x
  rw [minimalHopfInteriorBoundaryLiftRealizationHomotopyEquiv_toFun,
    minimalHopfBallInteriorBoundaryRealizationInclPuncturedHomotopyEquiv_toFun]
  rfl

/-- Up to the certified homotopy equivalence of domain spheres, the collapsed attaching map is
homotopic to the finite Hopf map. -/
theorem minimalHopfProjectivePlaneTargetAttachingMap_homotopic_finiteHopf :
    (minimalHopfRealizationMap.hom.comp
        minimalHopfAttachingDomainComparisonHomotopyEquiv.toFun).Homotopic
      minimalHopfProjectivePlaneTargetAttachingMap.hom := by
  rw [minimalHopfAttachingDomainComparisonHomotopyEquiv_toFun]
  exact ⟨minimalHopfAttachingMapHomotopyFiniteHopf⟩

end Submission.ComplexProjectivePlaneTriangulation
