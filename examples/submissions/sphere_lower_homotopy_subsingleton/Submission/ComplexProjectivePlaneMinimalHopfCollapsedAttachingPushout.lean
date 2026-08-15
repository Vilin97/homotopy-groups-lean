/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfTargetCollapse
import Submission.SSetMonoRealizationCofibration

/-!
# The collapsed four-simplex attaching pushout

The punctured nine-vertex projective plane collapses onto the finite Hopf target.  Transporting
the boundary map of its remaining four-simplex across that retraction gives a second, canonical
topological pushout.  This file constructs that pushout and the comparison from the realized
projective plane, records its two summand formulas, and proves that it is the identity on the
finite target.  The remaining gluing step is to promote this comparison to a homotopy
equivalence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped Topology Topology.Homotopy

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The pushout obtained by attaching the all-interior four-simplex directly to the finite Hopf
target along the collapsed attaching map. -/
noncomputable abbrev minimalHopfCollapsedAttachingPushout : TopCat :=
  Limits.pushout minimalHopfProjectivePlaneTargetAttachingMap
    (SSet.toTop.map
      minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex)

/-- Inclusion of the finite Hopf target into the collapsed attaching pushout. -/
noncomputable abbrev minimalHopfCollapsedAttachingPushoutTargetIncl :
    SSet.toTop.obj (orderedSSet minimalHopfTargetFacets) ⟶
      minimalHopfCollapsedAttachingPushout :=
  Limits.pushout.inl minimalHopfProjectivePlaneTargetAttachingMap
    (SSet.toTop.map
      minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex)

/-- Inclusion of the remaining four-simplex into the collapsed attaching pushout. -/
noncomputable abbrev minimalHopfCollapsedAttachingPushoutSimplexIncl :
    SSet.toTop.obj
        (orderedSSet minimalHopfProjectivePlaneInteriorSimplexFacets) ⟶
      minimalHopfCollapsedAttachingPushout :=
  Limits.pushout.inr minimalHopfProjectivePlaneTargetAttachingMap
    (SSet.toTop.map
      minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex)

/-- The canonical square defining the collapsed attaching space is a topological pushout. -/
theorem minimalHopfCollapsedAttachingPushout_isPushout :
    IsPushout minimalHopfProjectivePlaneTargetAttachingMap
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex)
      minimalHopfCollapsedAttachingPushoutTargetIncl
      minimalHopfCollapsedAttachingPushoutSimplexIncl :=
  IsPushout.of_hasPushout _ _

/-- The realized boundary inclusion into the remaining four-simplex is a cofibration. -/
theorem minimalHopfProjectivePlaneInteriorBoundaryRealizationInclSimplex_isCofibration :
    IsCofibration
      (SSet.toTop.map
        minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex) := by
  letI : Mono minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex := by
    unfold minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex
      orderedSSetHomOfFacetFamilyLE
    infer_instance
  exact Submission.geometricRealization_isCofibration_of_mono
    minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex

/-- The target inclusion into the collapsed attaching pushout is a cofibration, by cobase
change of the four-simplex boundary inclusion. -/
theorem minimalHopfCollapsedAttachingPushoutTargetIncl_isCofibration :
    IsCofibration minimalHopfCollapsedAttachingPushoutTargetIncl :=
  minimalHopfCollapsedAttachingPushout_isPushout.isCofibration
    minimalHopfProjectivePlaneInteriorBoundaryRealizationInclSimplex_isCofibration

/-- Collapse the punctured summand to the finite target and leave the remaining four-simplex
unchanged.  The two maps agree strictly on the boundary by definition of the collapsed attaching
map, so the projective-plane pushout supplies this canonical comparison. -/
noncomputable def minimalHopfProjectivePlaneToCollapsedAttachingPushout :
    projectivePlaneRealization ⟶ minimalHopfCollapsedAttachingPushout :=
  minimalHopfProjectivePlanePuncturedSimplexRealization_isPushout.desc
    (TopCat.ofHom
        minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun ≫
      minimalHopfCollapsedAttachingPushoutTargetIncl)
    minimalHopfCollapsedAttachingPushoutSimplexIncl
    (by
      rw [← Category.assoc]
      change minimalHopfProjectivePlaneTargetAttachingMap ≫
          minimalHopfCollapsedAttachingPushoutTargetIncl =
        SSet.toTop.map
            minimalHopfProjectivePlaneInteriorBoundarySSetInclSimplex ≫
          minimalHopfCollapsedAttachingPushoutSimplexIncl
      exact Limits.pushout.condition)

/-- On the punctured summand, the comparison is the collapse retraction followed by target
inclusion. -/
@[reassoc]
theorem minimalHopfProjectivePlanePuncturedIncl_toCollapsedAttachingPushout :
    SSet.toTop.map minimalHopfProjectivePlanePuncturedSSetIncl ≫
        minimalHopfProjectivePlaneToCollapsedAttachingPushout =
      TopCat.ofHom
          minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun ≫
        minimalHopfCollapsedAttachingPushoutTargetIncl := by
  apply minimalHopfProjectivePlanePuncturedSimplexRealization_isPushout.inl_desc

/-- On the four-simplex summand, the comparison is exactly the canonical pushout inclusion. -/
@[reassoc]
theorem minimalHopfProjectivePlaneInteriorSimplexIncl_toCollapsedAttachingPushout :
    SSet.toTop.map minimalHopfProjectivePlaneInteriorSimplexSSetIncl ≫
        minimalHopfProjectivePlaneToCollapsedAttachingPushout =
      minimalHopfCollapsedAttachingPushoutSimplexIncl := by
  apply minimalHopfProjectivePlanePuncturedSimplexRealization_isPushout.inr_desc

/-- The direct finite-target inclusion into the projective plane factors through the punctured
subcomplex. -/
theorem minimalHopfTargetSSetInclPunctured_comp_projectivePlanePuncturedSSetIncl :
    minimalHopfTargetSSetInclPunctured ≫
        minimalHopfProjectivePlanePuncturedSSetIncl =
      minimalHopfTargetSSetIncl := by
  rfl

/-- The projective-plane comparison is strictly the identity on the finite Hopf target. -/
@[reassoc]
theorem minimalHopfTargetIncl_toCollapsedAttachingPushout :
    SSet.toTop.map minimalHopfTargetSSetIncl ≫
        minimalHopfProjectivePlaneToCollapsedAttachingPushout =
      minimalHopfCollapsedAttachingPushoutTargetIncl := by
  rw [← minimalHopfTargetSSetInclPunctured_comp_projectivePlanePuncturedSSetIncl,
    SSet.toTop.map_comp, Category.assoc,
    minimalHopfProjectivePlanePuncturedIncl_toCollapsedAttachingPushout]
  rw [← Category.assoc]
  have hret :
      SSet.toTop.map minimalHopfTargetSSetInclPunctured ≫
          TopCat.ofHom
            minimalHopfTargetRealizationInclPuncturedHomotopyEquiv.invFun =
        𝟙 _ := by
    apply TopCat.hom_ext
    exact minimalHopfTargetRealizationInclPuncturedHomotopyEquiv_invFun_comp_incl
  rw [hret, Category.id_comp]

end Submission.ComplexProjectivePlaneTriangulation
