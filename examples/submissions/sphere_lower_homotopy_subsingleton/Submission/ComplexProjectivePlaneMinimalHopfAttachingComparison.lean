/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfBallBoundaryCollapse
import Submission.ComplexProjectivePlaneMinimalHopfTargetCollapse

/-!
# Comparing the collapsed attaching map with the finite Hopf map

The finite quotient restricts from the punctured seventeen-vertex ambient complex to the
punctured projective-plane complex.  Its two boundary restrictions are strict: on the original
boundary it is the certified finite Hopf map, and on the distinguished simplex boundary it is
the identity-coordinate inclusion.  The relative ambient collapse then supplies the domain
comparison used below.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped unitInterval Topology Topology.Homotopy

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## Restricting the finite quotient -/

/-- Every punctured ambient facet maps to a face of the punctured projective-plane complex. -/
theorem minimalHopfBallPuncturedFacetFamilyMapsTo :
    FacetFamilyMapsTo minimalHopfQuotientVertex
      minimalHopfBallPuncturedFacets
      minimalHopfProjectivePlanePuncturedFacets := by
  intro facet hfacet
  exact (by decide : ∀ f : {f // f ∈ minimalHopfBallPuncturedFacets},
    IsFace minimalHopfProjectivePlanePuncturedFacets
      (f.1.image minimalHopfQuotientVertex)) ⟨facet, hfacet⟩

/-- The finite quotient restricted to the two punctured complexes. -/
def minimalHopfBallPuncturedQuotientSSetMap :
    orderedSSet minimalHopfBallPuncturedFacets ⟶
      orderedSSet minimalHopfProjectivePlanePuncturedFacets :=
  orderedSSetMapOfMonotone minimalHopfQuotientVertex
    minimalHopfBallPuncturedFacetFamilyMapsTo

/-- On the original boundary, the punctured quotient is strictly the finite Hopf map followed
by target inclusion. -/
theorem minimalHopfBallPuncturedQuotient_boundary_sSet_square :
    minimalHopfSphereSSetInclBallPunctured ≫
        minimalHopfBallPuncturedQuotientSSetMap =
      minimalHopfSSetMap ≫ minimalHopfTargetSSetInclPunctured := by
  ext Δ x
  rfl

/-- The realized original-boundary quotient square commutes strictly. -/
theorem minimalHopfBallPuncturedQuotient_boundary_realization_square :
    SSet.toTop.map minimalHopfSphereSSetInclBallPunctured ≫
        SSet.toTop.map minimalHopfBallPuncturedQuotientSSetMap =
      SSet.toTop.map minimalHopfSSetMap ≫
        SSet.toTop.map minimalHopfTargetSSetInclPunctured := by
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp,
    minimalHopfBallPuncturedQuotient_boundary_sSet_square]

/-! ## The distinguished simplex boundary -/

/-- The distinguished all-interior simplex in the seventeen-vertex ambient complex. -/
def minimalHopfBallInteriorFacet : Finset MinimalHopfBallVertex :=
  {0, 1, 2, 3, 4}

/-- Its five-tetrahedron boundary. -/
def minimalHopfBallInteriorBoundaryFacets :
    Finset (Finset MinimalHopfBallVertex) :=
  simplexBoundaryFacets minimalHopfBallInteriorFacet

/-- The distinguished simplex boundary lies in the punctured ambient complex. -/
theorem minimalHopfBallInteriorBoundaryFacets_le_punctured :
    FacetFamilyLE minimalHopfBallInteriorBoundaryFacets
      minimalHopfBallPuncturedFacets := by
  intro facet hfacet
  exact (by decide : ∀ f : {f // f ∈ minimalHopfBallInteriorBoundaryFacets},
    IsFace minimalHopfBallPuncturedFacets f.1) ⟨facet, hfacet⟩

/-- Inclusion of the distinguished simplex boundary into the punctured ambient complex. -/
def minimalHopfBallInteriorBoundarySSetInclPunctured :
    orderedSSet minimalHopfBallInteriorBoundaryFacets ⟶
      orderedSSet minimalHopfBallPuncturedFacets :=
  orderedSSetHomOfFacetFamilyLE
    minimalHopfBallInteriorBoundaryFacets_le_punctured

/-- A monotone section of the quotient on the nine projective-plane vertices. -/
def minimalHopfQuotientVertexSection : Vertex ↪o MinimalHopfBallVertex where
  toFun := ![0, 1, 2, 3, 4, 5, 8, 11, 14]
  inj' := by decide
  map_rel_iff' := by decide

@[simp]
theorem minimalHopfQuotientVertex_section (v : Vertex) :
    minimalHopfQuotientVertex (minimalHopfQuotientVertexSection v) = v := by
  fin_cases v <;> rfl

/-- The section maps the projective-plane interior boundary into the ambient interior
boundary. -/
theorem minimalHopfInteriorBoundarySectionFacetFamilyMapsTo :
    FacetFamilyMapsTo minimalHopfQuotientVertexSection
      minimalHopfProjectivePlaneInteriorBoundaryFacets
      minimalHopfBallInteriorBoundaryFacets := by
  intro facet hfacet
  exact (by decide : ∀ f :
      {f // f ∈ minimalHopfProjectivePlaneInteriorBoundaryFacets},
    IsFace minimalHopfBallInteriorBoundaryFacets
      (f.1.image minimalHopfQuotientVertexSection)) ⟨facet, hfacet⟩

/-- Lift the projective-plane interior boundary to the identically numbered ambient boundary. -/
def minimalHopfInteriorBoundaryLiftSSetMap :
    orderedSSet minimalHopfProjectivePlaneInteriorBoundaryFacets ⟶
      orderedSSet minimalHopfBallInteriorBoundaryFacets :=
  orderedSSetMapOfMonotone minimalHopfQuotientVertexSection.toOrderHom
    minimalHopfInteriorBoundarySectionFacetFamilyMapsTo

/-- The quotient after the lifted interior-boundary inclusion is strictly the original
projective-plane interior-boundary inclusion. -/
theorem minimalHopfBallPuncturedQuotient_interiorBoundary_sSet_triangle :
    minimalHopfInteriorBoundaryLiftSSetMap ≫
        minimalHopfBallInteriorBoundarySSetInclPunctured ≫
          minimalHopfBallPuncturedQuotientSSetMap =
      minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured := by
  ext Δ x
  apply Subtype.ext
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  simp [minimalHopfInteriorBoundaryLiftSSetMap,
    minimalHopfBallInteriorBoundarySSetInclPunctured,
    minimalHopfBallPuncturedQuotientSSetMap,
    orderedSSetMapOfMonotone, orderedSSetHomOfFacetFamilyLE]
  change minimalHopfQuotientVertex
      (minimalHopfQuotientVertexSection (x.1.obj i)) = x.1.obj i
  exact minimalHopfQuotientVertex_section (x.1.obj i)

/-- The realized distinguished-boundary quotient triangle commutes strictly. -/
theorem minimalHopfBallPuncturedQuotient_interiorBoundary_realization_triangle :
    SSet.toTop.map minimalHopfInteriorBoundaryLiftSSetMap ≫
        SSet.toTop.map minimalHopfBallInteriorBoundarySSetInclPunctured ≫
          SSet.toTop.map minimalHopfBallPuncturedQuotientSSetMap =
      SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured := by
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp,
    minimalHopfBallPuncturedQuotient_interiorBoundary_sSet_triangle]

/-! ## The induced domain comparison -/

/-- Collapse the lifted distinguished boundary back to the original finite Hopf domain. -/
noncomputable def minimalHopfAttachingDomainComparison :
    SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlaneInteriorBoundaryFacets) ⟶
      SSet.toTop.obj (orderedSSet minimalHopfSphereFacets) :=
  SSet.toTop.map minimalHopfInteriorBoundaryLiftSSetMap ≫
    SSet.toTop.map minimalHopfBallInteriorBoundarySSetInclPunctured ≫
      TopCat.ofHom
        minimalHopfSphereRealizationInclBallPuncturedHomotopyEquiv.invFun

/-- Pointwise form of the realized original-boundary quotient square. -/
theorem minimalHopfBallPuncturedQuotient_boundary_realization_square_apply
    (x : SSet.toTop.obj (orderedSSet minimalHopfSphereFacets)) :
    SSet.toTop.map minimalHopfBallPuncturedQuotientSSetMap
        (SSet.toTop.map minimalHopfSphereSSetInclBallPunctured x) =
      SSet.toTop.map minimalHopfTargetSSetInclPunctured
        (SSet.toTop.map minimalHopfSSetMap x) := by
  simpa [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom
      minimalHopfBallPuncturedQuotient_boundary_realization_square x

/-- Pointwise form of the realized distinguished-boundary quotient triangle. -/
theorem minimalHopfBallPuncturedQuotient_interiorBoundary_realization_triangle_apply
    (x : SSet.toTop.obj
      (orderedSSet minimalHopfProjectivePlaneInteriorBoundaryFacets)) :
    SSet.toTop.map minimalHopfBallPuncturedQuotientSSetMap
        (SSet.toTop.map minimalHopfBallInteriorBoundarySSetInclPunctured
          (SSet.toTop.map minimalHopfInteriorBoundaryLiftSSetMap x)) =
      SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured x := by
  simpa [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom
      minimalHopfBallPuncturedQuotient_interiorBoundary_realization_triangle x

/-- The collapsed projective-plane attaching map is homotopic to the certified finite Hopf map
after the ambient relative collapse supplies the comparison of their domain spheres. -/
noncomputable def minimalHopfAttachingMapHomotopyFiniteHopf :
    ContinuousMap.Homotopy
      (minimalHopfRealizationMap.hom.comp
        minimalHopfAttachingDomainComparison.hom)
      minimalHopfProjectivePlaneTargetAttachingMap.hom where
  toFun p :=
    minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun
      (SSet.toTop.map minimalHopfBallPuncturedQuotientSSetMap
        (minimalHopfBallPuncturedRealizationDeformation
          (p.1,
            SSet.toTop.map minimalHopfBallInteriorBoundarySSetInclPunctured
              (SSet.toTop.map minimalHopfInteriorBoundaryLiftSSetMap p.2))))
  continuous_toFun :=
    minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun.continuous.comp
      ((SSet.toTop.map
          minimalHopfBallPuncturedQuotientSSetMap).hom.continuous.comp
        (minimalHopfBallPuncturedRealizationDeformation.continuous.comp
          (continuous_fst.prodMk
            ((SSet.toTop.map
                minimalHopfBallInteriorBoundarySSetInclPunctured).hom.continuous.comp
              ((SSet.toTop.map
                  minimalHopfInteriorBoundaryLiftSSetMap).hom.continuous.comp
                continuous_snd)))))
  map_zero_left x := by
    rw [ContinuousMap.Homotopy.apply_zero,
      minimalHopfSphereRealizationInclBallPuncturedHomotopyEquiv_toFun]
    change minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun
        (SSet.toTop.map minimalHopfBallPuncturedQuotientSSetMap
          (SSet.toTop.map minimalHopfSphereSSetInclBallPunctured
            (minimalHopfSphereRealizationInclBallPuncturedHomotopyEquiv.invFun
              (SSet.toTop.map minimalHopfBallInteriorBoundarySSetInclPunctured
                (SSet.toTop.map minimalHopfInteriorBoundaryLiftSSetMap x))))) =
      SSet.toTop.map minimalHopfSSetMap
        (minimalHopfSphereRealizationInclBallPuncturedHomotopyEquiv.invFun
          (SSet.toTop.map minimalHopfBallInteriorBoundarySSetInclPunctured
            (SSet.toTop.map minimalHopfInteriorBoundaryLiftSSetMap x)))
    rw [minimalHopfBallPuncturedQuotient_boundary_realization_square_apply]
    let y := SSet.toTop.map minimalHopfSSetMap
      (minimalHopfSphereRealizationInclBallPuncturedHomotopyEquiv.invFun
        (SSet.toTop.map minimalHopfBallInteriorBoundarySSetInclPunctured
          (SSet.toTop.map minimalHopfInteriorBoundaryLiftSSetMap x)))
    change minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun
        ((SSet.toTop.map minimalHopfTargetSSetInclPunctured).hom y) = y
    have hincl :
        (SSet.toTop.map minimalHopfTargetSSetInclPunctured).hom y =
          minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.toFun y :=
      congrArg (fun f ↦ f y)
        minimalHopfTargetRealizationInclPuncturedHomotopyEquiv_toFun.symm
    rw [hincl,
      minimalHopfTargetRealizationInclPuncturedHomotopyEquiv_invFun_toFun]
  map_one_left x := by
    rw [ContinuousMap.Homotopy.apply_one]
    change minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun
        (SSet.toTop.map minimalHopfBallPuncturedQuotientSSetMap
          (SSet.toTop.map minimalHopfBallInteriorBoundarySSetInclPunctured
            (SSet.toTop.map minimalHopfInteriorBoundaryLiftSSetMap x))) =
      minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun
        (SSet.toTop.map
          minimalHopfProjectivePlaneInteriorBoundarySSetInclPunctured x)
    rw [minimalHopfBallPuncturedQuotient_interiorBoundary_realization_triangle_apply]

end Submission.ComplexProjectivePlaneTriangulation
