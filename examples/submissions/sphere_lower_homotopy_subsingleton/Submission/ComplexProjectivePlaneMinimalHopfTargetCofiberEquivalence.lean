/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfCollapsedAttachingEquivalence
import Submission.ComplexProjectivePlaneMinimalHopfAmbientPushout
import Submission.Topology.MappingConeHomotopy

/-!
# The finite Hopf target cofiber is preserved by the collapsed attachment comparison

The canonical homotopy equivalence from the realized nine-vertex projective plane to its
collapsed attaching pushout is an equivalence under the finite Hopf target.  Its two
inverse-composite homotopies fix that target pointwise.  Consequently it induces an explicit
homotopy equivalence between the mapping cones of the two target inclusions.
-/

noncomputable section

open CategoryTheory Simplicial TopCat
open scoped unitInterval Topology Topology.Homotopy

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The cofiber of the finite Hopf target inclusion into the collapsed attaching pushout. -/
noncomputable abbrev minimalHopfCollapsedAttachingTargetCofiber : TopCat :=
  topologicalMappingCone minimalHopfCollapsedAttachingPushoutTargetIncl

/-- The inverse comparison commutes strictly with the finite Hopf target inclusion. -/
theorem minimalHopfCollapsedAttachingTargetIncl_toProjectivePlane :
    minimalHopfCollapsedAttachingPushoutTargetIncl ≫
        minimalHopfCollapsedAttachingPushoutToProjectivePlane =
      SSet.toTop.map minimalHopfTargetSSetIncl := by
  rw [minimalHopfCollapsedAttachingInverse_target,
    minimalHopfCollapsedAttachingTargetToProjectivePlane_eq_targetIncl]

/-- The map of target cofibers induced by the canonical collapsed-attachment comparison. -/
noncomputable def minimalHopfProjectivePlaneTargetCofiberToCollapsed :
    minimalHopfProjectivePlaneTargetCofiber ⟶
      minimalHopfCollapsedAttachingTargetCofiber :=
  topologicalMappingConeMap
    (SSet.toTop.map minimalHopfTargetSSetIncl)
    minimalHopfCollapsedAttachingPushoutTargetIncl
    (𝟙 (SSet.toTop.obj (orderedSSet minimalHopfTargetFacets)))
    minimalHopfProjectivePlaneToCollapsedAttachingPushout
    (by simpa using minimalHopfTargetIncl_toCollapsedAttachingPushout)

/-- The inverse map of target cofibers induced by the inverse collapsed-attachment comparison. -/
noncomputable def minimalHopfCollapsedAttachingTargetCofiberToProjectivePlane :
    minimalHopfCollapsedAttachingTargetCofiber ⟶
      minimalHopfProjectivePlaneTargetCofiber :=
  topologicalMappingConeMap
    minimalHopfCollapsedAttachingPushoutTargetIncl
    (SSet.toTop.map minimalHopfTargetSSetIncl)
    (𝟙 (SSet.toTop.obj (orderedSSet minimalHopfTargetFacets)))
    minimalHopfCollapsedAttachingPushoutToProjectivePlane
    (by simpa using minimalHopfCollapsedAttachingTargetIncl_toProjectivePlane)

@[reassoc]
theorem minimalHopfProjectivePlaneTargetCofiberToCollapsed_target :
    topologicalMappingConeIncl (SSet.toTop.map minimalHopfTargetSSetIncl) ≫
        minimalHopfProjectivePlaneTargetCofiberToCollapsed =
      minimalHopfProjectivePlaneToCollapsedAttachingPushout ≫
        topologicalMappingConeIncl minimalHopfCollapsedAttachingPushoutTargetIncl := by
  apply topologicalMappingConeIncl_map

@[reassoc]
theorem minimalHopfCollapsedAttachingTargetCofiberToProjectivePlane_target :
    topologicalMappingConeIncl minimalHopfCollapsedAttachingPushoutTargetIncl ≫
        minimalHopfCollapsedAttachingTargetCofiberToProjectivePlane =
      minimalHopfCollapsedAttachingPushoutToProjectivePlane ≫
        topologicalMappingConeIncl (SSet.toTop.map minimalHopfTargetSSetIncl) := by
  apply topologicalMappingConeIncl_map

@[reassoc]
theorem minimalHopfProjectivePlaneTargetCofiberToCollapsed_cone :
    topologicalMappingConeConeIncl (SSet.toTop.map minimalHopfTargetSSetIncl) ≫
        minimalHopfProjectivePlaneTargetCofiberToCollapsed =
      topologicalMappingConeConeIncl minimalHopfCollapsedAttachingPushoutTargetIncl := by
  have h := topologicalMappingConeConeIncl_map
    (SSet.toTop.map minimalHopfTargetSSetIncl)
    minimalHopfCollapsedAttachingPushoutTargetIncl
    (𝟙 (SSet.toTop.obj (orderedSSet minimalHopfTargetFacets)))
    minimalHopfProjectivePlaneToCollapsedAttachingPushout
    (by simpa using minimalHopfTargetIncl_toCollapsedAttachingPushout)
  simpa only [minimalHopfProjectivePlaneTargetCofiberToCollapsed,
    topologicalConeMap_id, Category.id_comp] using h

@[reassoc]
theorem minimalHopfCollapsedAttachingTargetCofiberToProjectivePlane_cone :
    topologicalMappingConeConeIncl minimalHopfCollapsedAttachingPushoutTargetIncl ≫
        minimalHopfCollapsedAttachingTargetCofiberToProjectivePlane =
      topologicalMappingConeConeIncl (SSet.toTop.map minimalHopfTargetSSetIncl) := by
  have h := topologicalMappingConeConeIncl_map
    minimalHopfCollapsedAttachingPushoutTargetIncl
    (SSet.toTop.map minimalHopfTargetSSetIncl)
    (𝟙 (SSet.toTop.obj (orderedSSet minimalHopfTargetFacets)))
    minimalHopfCollapsedAttachingPushoutToProjectivePlane
    (by simpa using minimalHopfCollapsedAttachingTargetIncl_toProjectivePlane)
  simpa only [minimalHopfCollapsedAttachingTargetCofiberToProjectivePlane,
    topologicalConeMap_id, Category.id_comp] using h

/-- The target-relative collapsed-attachment equivalence induces a homotopy equivalence of
the two target cofibers. -/
noncomputable def minimalHopfProjectivePlaneTargetCofiberHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      minimalHopfProjectivePlaneTargetCofiber
      minimalHopfCollapsedAttachingTargetCofiber :=
  topologicalMappingConeHomotopyEquiv
    (SSet.toTop.map minimalHopfTargetSSetIncl)
    minimalHopfCollapsedAttachingPushoutTargetIncl
    minimalHopfProjectivePlaneToCollapsedAttachingPushout
    minimalHopfCollapsedAttachingPushoutToProjectivePlane
    minimalHopfTargetIncl_toCollapsedAttachingPushout
    minimalHopfCollapsedAttachingTargetIncl_toProjectivePlane
    minimalHopfCollapsedAttachingProjectivePlaneHomotopyForward
    minimalHopfCollapsedAttachingPushoutHomotopyForward
    minimalHopfCollapsedAttachingProjectivePlaneHomotopyForward_target
    minimalHopfCollapsedAttachingPushoutHomotopyForward_target

theorem minimalHopfProjectivePlaneTargetCofiberHomotopyEquiv_toFun :
    minimalHopfProjectivePlaneTargetCofiberHomotopyEquiv.toFun =
      minimalHopfProjectivePlaneTargetCofiberToCollapsed.hom :=
  rfl

theorem minimalHopfProjectivePlaneTargetCofiberHomotopyEquiv_invFun :
    minimalHopfProjectivePlaneTargetCofiberHomotopyEquiv.invFun =
      minimalHopfCollapsedAttachingTargetCofiberToProjectivePlane.hom :=
  rfl

end Submission.ComplexProjectivePlaneTriangulation
