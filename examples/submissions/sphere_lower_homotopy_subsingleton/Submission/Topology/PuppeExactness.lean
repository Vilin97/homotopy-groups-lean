/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.PuppeFlattening

/-!
# Rotated exactness for the Puppe comparison

The full second-Puppe homotopy equivalence reflects nullhomotopies.  Consequently the bottom
inclusion into the second mapping cone is nullhomotopic exactly when the suspended attaching
map is, and the generic cofiber-retraction criterion can be rotated one step farther around the
Puppe sequence.
-/

open CategoryTheory
open scoped ContinuousMap Topology TopCat

noncomputable section

namespace Submission

universe u v w

/-- Postcomposition by a homotopy equivalence reflects and preserves nullhomotopies. -/
theorem nullhomotopic_comp_homotopyEquiv_iff
    {W : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(W, X)) (e : X ≃ₕ Y) :
    (e.toFun.comp f).Nullhomotopic ↔ f.Nullhomotopic := by
  constructor
  · intro h
    have hback : (e.invFun.comp (e.toFun.comp f)).Nullhomotopic :=
      h.comp_right e.invFun
    have H : (e.invFun.comp e.toFun).comp f |>.Homotopic f := by
      simpa using e.left_inv.comp (ContinuousMap.Homotopic.refl f)
    rw [← ContinuousMap.comp_assoc] at hback
    obtain ⟨x, hx⟩ := hback
    exact ⟨x, H.symm.trans hx⟩
  · exact fun h ↦ h.comp_right e.toFun

variable {A X : TopCat.{u}}

/-- The bottom inclusion into the second mapping cone is nullhomotopic exactly when the
suspension of the original attaching map is nullhomotopic. -/
theorem topologicalSecondMappingConeIncl_nullhomotopic_iff_suspensionMap
    (f : A ⟶ X) :
    (topologicalMappingConeIncl
        (topologicalMappingConeCollapse f)).hom.Nullhomotopic ↔
      (topologicalSuspensionMap A f).hom.Nullhomotopic := by
  rw [← topologicalSecondMappingConeIncl_toSuspension f]
  exact (nullhomotopic_comp_homotopyEquiv_iff
    (topologicalMappingConeIncl (topologicalMappingConeCollapse f)).hom
    (topologicalSecondMappingConeHomotopyEquivSuspension f)).symm

/-- Rotated cofiber exactness: the collapse out of the second mapping cone has a homotopy
retraction exactly when the original attaching map becomes null after suspension. -/
theorem exists_topologicalSecondMappingConeCollapse_homotopy_retraction_iff
    (f : A ⟶ X) :
    (∃ r : topologicalSuspension (topologicalMappingCone f) ⟶
          topologicalMappingCone (topologicalMappingConeCollapse f),
        Nonempty (TopCat.Homotopy
          (topologicalMappingConeCollapse (topologicalMappingConeCollapse f) ≫ r)
          (𝟙 (topologicalMappingCone (topologicalMappingConeCollapse f))))) ↔
      (topologicalSuspensionMap A f).hom.Nullhomotopic := by
  rw [exists_topologicalMappingConeCollapse_homotopy_retraction_iff_incl_nullhomotopic,
    topologicalSecondMappingConeIncl_nullhomotopic_iff_suspensionMap]

end Submission
