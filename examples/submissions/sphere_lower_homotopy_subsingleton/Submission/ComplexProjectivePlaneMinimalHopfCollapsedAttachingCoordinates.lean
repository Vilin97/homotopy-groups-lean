/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfCollapsedAttachingEquivalence
import Submission.FiniteOrderedSimplexRealization

/-!
# Sphere coordinates for the collapsed projective-plane attaching map

The boundary of the retained four-simplex and the finite Hopf target are transported to the
exact metric three- and two-spheres.  This packages the collapsed attaching map as a concrete
map `S³ → S²`; identifying it with the separately certified finite Hopf map remains a distinct
geometric comparison.
-/

noncomputable section

open CategoryTheory Simplicial TopCat

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The retained projective-plane four-simplex has five vertices. -/
theorem minimalHopfProjectivePlaneInteriorFacet_card :
    minimalHopfProjectivePlaneInteriorFacet.card = 4 + 1 := by
  decide

/-- The boundary of the retained four-simplex is the standard simplicial three-sphere. -/
noncomputable def minimalHopfProjectivePlaneInteriorBoundarySSetIsoBoundaryFour :
    orderedSSet minimalHopfProjectivePlaneInteriorBoundaryFacets ≅
      (SSet.boundary 4 : SSet) :=
  simplexBoundarySSetIso 4 minimalHopfProjectivePlaneInteriorFacet
    minimalHopfProjectivePlaneInteriorFacet_card

/-- Exact metric-three-sphere coordinates on the boundary of the retained four-simplex. -/
noncomputable def minimalHopfProjectivePlaneInteriorBoundaryRealizationHomeomorphSphereThree :
    SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlaneInteriorBoundaryFacets) ≃ₜ
      SphereSpace 3 :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso
        minimalHopfProjectivePlaneInteriorBoundarySSetIsoBoundaryFour)).trans
    (boundaryRealizationHomeomorphSphere 3)

/-- Exact closed-four-disk coordinates on the retained four-simplex. -/
noncomputable def minimalHopfProjectivePlaneInteriorSimplexRealizationHomeomorphDiskFour :
    SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlaneInteriorSimplexFacets) ≃ₜ
      TopCat.disk 4 :=
  simplexRealizationHomeomorphDisk 4 minimalHopfProjectivePlaneInteriorFacet
    minimalHopfProjectivePlaneInteriorFacet_card

/-- The collapsed attaching map in exact metric-sphere coordinates. -/
noncomputable def minimalHopfProjectivePlaneTargetAttachingSphereMap :
    TopCat.of (SphereSpace 3) ⟶ TopCat.of (SphereSpace 2) :=
  (TopCat.isoOfHomeo
      minimalHopfProjectivePlaneInteriorBoundaryRealizationHomeomorphSphereThree).inv ≫
    minimalHopfProjectivePlaneTargetAttachingMap ≫
      (TopCat.isoOfHomeo
        minimalHopfTargetRealizationHomeomorphSphereTwo).hom

/-- Transporting into and then out of sphere coordinates recovers the collapsed attaching map. -/
theorem minimalHopfProjectivePlaneTargetAttachingSphereMap_coordinates :
    (TopCat.isoOfHomeo
          minimalHopfProjectivePlaneInteriorBoundaryRealizationHomeomorphSphereThree).hom ≫
        minimalHopfProjectivePlaneTargetAttachingSphereMap ≫
      (TopCat.isoOfHomeo
        minimalHopfTargetRealizationHomeomorphSphereTwo).inv =
    minimalHopfProjectivePlaneTargetAttachingMap := by
  simp only [minimalHopfProjectivePlaneTargetAttachingSphereMap,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

end Submission.ComplexProjectivePlaneTriangulation
