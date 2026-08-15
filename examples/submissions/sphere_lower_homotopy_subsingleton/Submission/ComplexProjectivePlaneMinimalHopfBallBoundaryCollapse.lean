/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfBallBoundaryCollapseCertificate

/-!
# Relative collapse of the punctured finite Hopf ball onto its boundary

The 252-move certificate is promoted here to a homotopy equivalence from the punctured
seventeen-vertex ambient complex to the original finite Hopf domain.  Its inverse is the
literal boundary inclusion, and the associated deformation fixes that inclusion pointwise.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped unitInterval Topology Topology.Homotopy

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The computed endpoint carrier is canonically homeomorphic to the maintained finite Hopf
boundary carrier. -/
def minimalHopfBallBoundaryCollapseResultCarrierHomeomorph :
    facetFamilyCarrier
        (applyElementaryCollapseMoves minimalHopfBallPuncturedFacets
          minimalHopfBallBoundaryCollapseMoves) ≃ₜ
      facetFamilyCarrier minimalHopfSphereFacets where
  toFun := facetFamilyCarrierMapOfFacetFamilyLE (by
    rw [minimalHopfBallBoundaryCollapseMoves_result]
    exact minimalHopfBallBoundaryCollapsePresentation_le_sphere)
  invFun := facetFamilyCarrierMapOfFacetFamilyLE (by
    rw [minimalHopfBallBoundaryCollapseMoves_result]
    exact minimalHopfSphereFacets_le_ballBoundaryCollapsePresentation)
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_facetFamilyCarrierMapOfFacetFamilyLE (by
    rw [minimalHopfBallBoundaryCollapseMoves_result]
    exact minimalHopfBallBoundaryCollapsePresentation_le_sphere)
  continuous_invFun := continuous_facetFamilyCarrierMapOfFacetFamilyLE (by
    rw [minimalHopfBallBoundaryCollapseMoves_result]
    exact minimalHopfSphereFacets_le_ballBoundaryCollapsePresentation)

/-- The punctured finite Hopf ambient carrier is homotopy equivalent to its original boundary
carrier. -/
def minimalHopfBallPuncturedCarrierHomotopyEquivBoundary :
    ContinuousMap.HomotopyEquiv
      (facetFamilyCarrier minimalHopfBallPuncturedFacets)
      (facetFamilyCarrier minimalHopfSphereFacets) :=
  (elementaryCollapseMoveSequenceCarrierHomotopyEquiv
      minimalHopfBallPuncturedFacets
      minimalHopfBallBoundaryCollapseMoves
      minimalHopfBallBoundaryCollapseMoves_valid).trans
    minimalHopfBallBoundaryCollapseResultCarrierHomeomorph.toHomotopyEquiv

/-- The original finite Hopf boundary is a subcomplex of the punctured ambient complex. -/
theorem minimalHopfSphereFacets_le_ballPunctured :
    FacetFamilyLE minimalHopfSphereFacets minimalHopfBallPuncturedFacets := by
  intro facet hfacet
  exact (by decide : ∀ f : {f // f ∈ minimalHopfSphereFacets},
    IsFace minimalHopfBallPuncturedFacets f.1) ⟨facet, hfacet⟩

/-- The literal affine-carrier inclusion of the finite Hopf boundary into the punctured ambient
complex. -/
def minimalHopfSphereCarrierInclBallPunctured :
    C(facetFamilyCarrier minimalHopfSphereFacets,
      facetFamilyCarrier minimalHopfBallPuncturedFacets) :=
  ⟨facetFamilyCarrierMapOfFacetFamilyLE
      minimalHopfSphereFacets_le_ballPunctured,
    continuous_facetFamilyCarrierMapOfFacetFamilyLE
      minimalHopfSphereFacets_le_ballPunctured⟩

/-- The inverse in the collapse equivalence is exactly the literal boundary inclusion. -/
theorem minimalHopfBallPuncturedCarrierHomotopyEquivBoundary_invFun :
    minimalHopfBallPuncturedCarrierHomotopyEquivBoundary.invFun =
      minimalHopfSphereCarrierInclBallPunctured := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact elementaryCollapseMoveSequenceCarrierHomotopyEquiv_invFun_val
    minimalHopfBallPuncturedFacets
    minimalHopfBallBoundaryCollapseMoves
    minimalHopfBallBoundaryCollapseMoves_valid
    (minimalHopfBallBoundaryCollapseResultCarrierHomeomorph.symm x)

/-- The relative collapse retraction is strictly the identity on the included finite Hopf
boundary. -/
theorem minimalHopfBallPuncturedCarrierHomotopyEquivBoundary_toFun_incl
    (x : facetFamilyCarrier minimalHopfSphereFacets) :
    minimalHopfBallPuncturedCarrierHomotopyEquivBoundary.toFun
        (minimalHopfSphereCarrierInclBallPunctured x) = x := by
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff minimalHopfSphereFacets x.1).mp x.2
  apply Subtype.ext
  exact elementaryCollapseMoveSequenceCarrierHomotopyEquiv_toFun_val_eq_of_support
    minimalHopfBallPuncturedFacets
    minimalHopfBallBoundaryCollapseMoves
    minimalHopfBallBoundaryCollapseMoves_valid
    facet
    (fun move hmove ↦
      minimalHopfBallBoundaryCollapseMoves_relative move hmove facet hfacet)
    (minimalHopfSphereCarrierInclBallPunctured x)
    hsupport

/-- As continuous maps, collapse after boundary inclusion is strictly the identity. -/
theorem minimalHopfBallPuncturedCarrierHomotopyEquivBoundary_toFun_comp_incl :
    minimalHopfBallPuncturedCarrierHomotopyEquivBoundary.toFun.comp
        minimalHopfSphereCarrierInclBallPunctured =
      ContinuousMap.id (facetFamilyCarrier minimalHopfSphereFacets) := by
  apply ContinuousMap.ext
  exact minimalHopfBallPuncturedCarrierHomotopyEquivBoundary_toFun_incl

/-- The literal boundary inclusion into the punctured ambient carrier is a homotopy
equivalence. -/
def minimalHopfSphereCarrierInclBallPuncturedHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (facetFamilyCarrier minimalHopfSphereFacets)
      (facetFamilyCarrier minimalHopfBallPuncturedFacets) :=
  minimalHopfBallPuncturedCarrierHomotopyEquivBoundary.symm

/-- The forward map of the boundary-inclusion homotopy equivalence is the literal inclusion. -/
theorem minimalHopfSphereCarrierInclBallPuncturedHomotopyEquiv_toFun :
    minimalHopfSphereCarrierInclBallPuncturedHomotopyEquiv.toFun =
      minimalHopfSphereCarrierInclBallPunctured :=
  minimalHopfBallPuncturedCarrierHomotopyEquivBoundary_invFun

/-- The simplicial boundary inclusion into the punctured ambient complex. -/
def minimalHopfSphereSSetInclBallPunctured :
    orderedSSet minimalHopfSphereFacets ⟶
      orderedSSet minimalHopfBallPuncturedFacets :=
  orderedSSetHomOfFacetFamilyLE minimalHopfSphereFacets_le_ballPunctured

/-- The realized boundary inclusion into the punctured ambient complex is a homotopy
equivalence. -/
def minimalHopfSphereRealizationInclBallPuncturedHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (orderedSSet minimalHopfSphereFacets))
      (SSet.toTop.obj (orderedSSet minimalHopfBallPuncturedFacets)) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfSphereFacets).toHomotopyEquiv.trans
    (minimalHopfSphereCarrierInclBallPuncturedHomotopyEquiv.trans
      (orderedRealizationHomeomorphFacetFamilyCarrier
        minimalHopfBallPuncturedFacets).symm.toHomotopyEquiv)

/-- The forward map of the realized relative-collapse equivalence is the literal simplicial
boundary inclusion. -/
theorem minimalHopfSphereRealizationInclBallPuncturedHomotopyEquiv_toFun :
    minimalHopfSphereRealizationInclBallPuncturedHomotopyEquiv.toFun =
      (SSet.toTop.map minimalHopfSphereSSetInclBallPunctured).hom := by
  apply ContinuousMap.ext
  intro x
  change (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfBallPuncturedFacets).symm
        (minimalHopfSphereCarrierInclBallPuncturedHomotopyEquiv.toFun
          (orderedRealizationHomeomorphFacetFamilyCarrier
            minimalHopfSphereFacets x)) =
      SSet.toTop.map minimalHopfSphereSSetInclBallPunctured x
  rw [minimalHopfSphereCarrierInclBallPuncturedHomotopyEquiv_toFun]
  apply (orderedRealizationHomeomorphFacetFamilyCarrier
    minimalHopfBallPuncturedFacets).injective
  rw [Homeomorph.apply_symm_apply]
  simpa [minimalHopfSphereSSetInclBallPunctured,
    ConcreteCategory.comp_apply, facetFamilyCarrierHomOfFacetFamilyLE,
    minimalHopfSphereCarrierInclBallPunctured,
    orderedRealizationHomeomorphFacetFamilyCarrier] using
    (ConcreteCategory.congr_hom
      (orderedRealizationToFacetFamilyCarrier_naturality
        minimalHopfSphereFacets_le_ballPunctured) x).symm

/-- The explicit strong deformation from boundary-inclusion-after-collapse back to the
identity on the punctured affine carrier. -/
noncomputable def minimalHopfBallPuncturedCarrierDeformation :
    ContinuousMap.Homotopy
      (minimalHopfBallPuncturedCarrierHomotopyEquivBoundary.invFun.comp
        minimalHopfBallPuncturedCarrierHomotopyEquivBoundary.toFun)
      (ContinuousMap.id (facetFamilyCarrier minimalHopfBallPuncturedFacets)) := by
  let e := elementaryCollapseMoveSequenceCarrierHomotopyEquiv
    minimalHopfBallPuncturedFacets
    minimalHopfBallBoundaryCollapseMoves
    minimalHopfBallBoundaryCollapseMoves_valid
  let h := minimalHopfBallBoundaryCollapseResultCarrierHomeomorph
  let H := elementaryCollapseMoveSequenceCarrierDeformation
    minimalHopfBallPuncturedFacets
    minimalHopfBallBoundaryCollapseMoves
    minimalHopfBallBoundaryCollapseMoves_valid
  have hstart : e.invFun.comp e.toFun =
      minimalHopfBallPuncturedCarrierHomotopyEquivBoundary.invFun.comp
        minimalHopfBallPuncturedCarrierHomotopyEquivBoundary.toFun := by
    apply ContinuousMap.ext
    intro x
    change e.invFun (e.toFun x) = e.invFun (h.symm (h (e.toFun x)))
    rw [Homeomorph.symm_apply_apply]
  exact H.cast hstart rfl

/-- The punctured-carrier collapse retraction is constant throughout its explicit
deformation. -/
theorem minimalHopfBallPuncturedCarrierDeformation_toFun
    (t : I) (x : facetFamilyCarrier minimalHopfBallPuncturedFacets) :
    minimalHopfBallPuncturedCarrierHomotopyEquivBoundary.toFun
        (minimalHopfBallPuncturedCarrierDeformation (t, x)) =
      minimalHopfBallPuncturedCarrierHomotopyEquivBoundary.toFun x := by
  let e := elementaryCollapseMoveSequenceCarrierHomotopyEquiv
    minimalHopfBallPuncturedFacets
    minimalHopfBallBoundaryCollapseMoves
    minimalHopfBallBoundaryCollapseMoves_valid
  let h := minimalHopfBallBoundaryCollapseResultCarrierHomeomorph
  let H := elementaryCollapseMoveSequenceCarrierDeformation
    minimalHopfBallPuncturedFacets
    minimalHopfBallBoundaryCollapseMoves
    minimalHopfBallBoundaryCollapseMoves_valid
  apply Subtype.ext
  change (h (e.toFun (H (t, x)))).1 = (h (e.toFun x)).1
  exact congrArg (fun y ↦ (h y).1)
    (elementaryCollapseMoveSequenceCarrierDeformation_toFun
      minimalHopfBallPuncturedFacets
      minimalHopfBallBoundaryCollapseMoves
      minimalHopfBallBoundaryCollapseMoves_valid t x)

/-- The explicit punctured-carrier deformation fixes the included finite Hopf boundary
pointwise. -/
theorem minimalHopfBallPuncturedCarrierDeformation_incl
    (t : I) (x : facetFamilyCarrier minimalHopfSphereFacets) :
    minimalHopfBallPuncturedCarrierDeformation
        (t, minimalHopfSphereCarrierInclBallPunctured x) =
      minimalHopfSphereCarrierInclBallPunctured x := by
  let H := elementaryCollapseMoveSequenceCarrierDeformation
    minimalHopfBallPuncturedFacets
    minimalHopfBallBoundaryCollapseMoves
    minimalHopfBallBoundaryCollapseMoves_valid
  change H (t, minimalHopfSphereCarrierInclBallPunctured x) =
    minimalHopfSphereCarrierInclBallPunctured x
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff minimalHopfSphereFacets x.1).mp x.2
  exact elementaryCollapseMoveSequenceCarrierDeformation_eq_self_of_support
    minimalHopfBallPuncturedFacets
    minimalHopfBallBoundaryCollapseMoves
    minimalHopfBallBoundaryCollapseMoves_valid
    facet
    (fun move hmove ↦
      minimalHopfBallBoundaryCollapseMoves_relative move hmove facet hfacet)
    t
    (minimalHopfSphereCarrierInclBallPunctured x)
    hsupport

/-- The relative collapse transported to geometric realization as an explicit strong
deformation. -/
noncomputable def minimalHopfBallPuncturedRealizationDeformation :
    ContinuousMap.Homotopy
      (minimalHopfSphereRealizationInclBallPuncturedHomotopyEquiv.toFun.comp
        minimalHopfSphereRealizationInclBallPuncturedHomotopyEquiv.invFun)
      (ContinuousMap.id
        (SSet.toTop.obj (orderedSSet minimalHopfBallPuncturedFacets))) where
  toFun p :=
    (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfBallPuncturedFacets).symm
        (minimalHopfBallPuncturedCarrierDeformation
          (p.1, orderedRealizationHomeomorphFacetFamilyCarrier
            minimalHopfBallPuncturedFacets p.2))
  continuous_toFun :=
    (orderedRealizationHomeomorphFacetFamilyCarrier
        minimalHopfBallPuncturedFacets).symm.continuous.comp
      (minimalHopfBallPuncturedCarrierDeformation.continuous.comp
        (continuous_fst.prodMk
          ((orderedRealizationHomeomorphFacetFamilyCarrier
            minimalHopfBallPuncturedFacets).continuous.comp continuous_snd)))
  map_zero_left x := by
    let hp := orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfBallPuncturedFacets
    let hb := orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfSphereFacets
    let e := minimalHopfBallPuncturedCarrierHomotopyEquivBoundary
    change hp.symm
      (minimalHopfBallPuncturedCarrierDeformation (0, hp x)) = _
    rw [ContinuousMap.Homotopy.apply_zero]
    change hp.symm (e.invFun (e.toFun (hp x))) =
      hp.symm (e.invFun (hb (hb.symm (e.toFun (hp x)))))
    rw [Homeomorph.apply_symm_apply]
  map_one_left x := by
    change (orderedRealizationHomeomorphFacetFamilyCarrier
        minimalHopfBallPuncturedFacets).symm
      (minimalHopfBallPuncturedCarrierDeformation
        (1, orderedRealizationHomeomorphFacetFamilyCarrier
          minimalHopfBallPuncturedFacets x)) = x
    rw [ContinuousMap.Homotopy.apply_one]
    exact (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfBallPuncturedFacets).symm_apply_apply x

/-- The realized punctured-complex deformation fixes the included finite Hopf boundary
pointwise. -/
theorem minimalHopfBallPuncturedRealizationDeformation_incl
    (t : I)
    (x : SSet.toTop.obj (orderedSSet minimalHopfSphereFacets)) :
    minimalHopfBallPuncturedRealizationDeformation
        (t, SSet.toTop.map minimalHopfSphereSSetInclBallPunctured x) =
      SSet.toTop.map minimalHopfSphereSSetInclBallPunctured x := by
  let hp := orderedRealizationHomeomorphFacetFamilyCarrier
    minimalHopfBallPuncturedFacets
  let hb := orderedRealizationHomeomorphFacetFamilyCarrier
    minimalHopfSphereFacets
  have hcoord :
      hp (SSet.toTop.map minimalHopfSphereSSetInclBallPunctured x) =
        minimalHopfSphereCarrierInclBallPunctured (hb x) := by
    simpa [hp, hb, minimalHopfSphereSSetInclBallPunctured,
      ConcreteCategory.comp_apply, facetFamilyCarrierHomOfFacetFamilyLE,
      minimalHopfSphereCarrierInclBallPunctured,
      orderedRealizationHomeomorphFacetFamilyCarrier] using
      ConcreteCategory.congr_hom
        (orderedRealizationToFacetFamilyCarrier_naturality
          minimalHopfSphereFacets_le_ballPunctured) x
  change hp.symm
      (minimalHopfBallPuncturedCarrierDeformation
        (t, hp (SSet.toTop.map minimalHopfSphereSSetInclBallPunctured x))) =
    SSet.toTop.map minimalHopfSphereSSetInclBallPunctured x
  apply hp.injective
  rw [Homeomorph.apply_symm_apply, hcoord,
    minimalHopfBallPuncturedCarrierDeformation_incl]

end Submission.ComplexProjectivePlaneTriangulation
