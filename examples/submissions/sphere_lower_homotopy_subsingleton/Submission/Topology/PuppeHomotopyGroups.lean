/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.PuppeComparison
import Submission.Lean4TwentyResults

/-!
# Homotopy groups of the second Puppe comparison

The explicit section of the comparison

`C_(C_f -> Sigma A) -> Sigma X`

splits every induced map on homotopy groups.  This file records the natural suspension-point
basepoints and the resulting surjectivity and injectivity statements in every dimension.
-/

open CategoryTheory
open scoped Topology TopCat
open HomotopyGroups

noncomputable section

namespace Submission

universe u v

variable {A X : TopCat.{u}}

/-- The distinguished point-summand basepoint of the unreduced suspension. -/
def topologicalSuspensionBasepoint (A : TopCat.{u}) : topologicalSuspension A :=
  topologicalSuspensionPointIncl A PUnit.unit

/-- The distinguished target-summand basepoint of the second mapping cone. -/
def topologicalSecondMappingConeBasepoint (f : A ⟶ X) :
    topologicalMappingCone (topologicalMappingConeCollapse f) :=
  topologicalMappingConeIncl (topologicalMappingConeCollapse f)
    (topologicalSuspensionBasepoint A)

@[simp]
theorem topologicalSecondMappingConeToSuspension_basepoint (f : A ⟶ X) :
    topologicalSecondMappingConeToSuspension f
        (topologicalSecondMappingConeBasepoint f) =
      topologicalSuspensionBasepoint X := by
  have h :
      topologicalSuspensionPointIncl A ≫
          topologicalMappingConeIncl (topologicalMappingConeCollapse f) ≫
            topologicalSecondMappingConeToSuspension f =
        topologicalSuspensionPointIncl X := by
    rw [topologicalSecondMappingConeIncl_toSuspension,
      topologicalSuspensionPointIncl_map]
  exact ConcreteCategory.congr_hom h PUnit.unit

@[simp]
theorem topologicalSuspensionToSecondMappingCone_basepoint (f : A ⟶ X) :
    topologicalSuspensionToSecondMappingCone f
        (topologicalSuspensionBasepoint X) =
      topologicalSecondMappingConeBasepoint f := by
  simp only [topologicalSecondMappingConeBasepoint,
    topologicalSuspensionBasepoint, ← ConcreteCategory.comp_apply,
    topologicalSuspensionPointIncl_toSecondMappingCone]

/-- The second Puppe comparison is surjective on every homotopy group. -/
theorem topologicalSecondMappingConeToSuspension_homotopyGroup_surjective
    (N : Type v) (f : A ⟶ X) :
    Function.Surjective
      (HomotopyGroup.map (N := N)
        (topologicalSecondMappingConeToSuspension f).hom
        (topologicalSecondMappingConeToSuspension_basepoint f)) := by
  apply homotopyGroup_section_surjective
    (topologicalSecondMappingConeToSuspension f).hom
    (topologicalSuspensionToSecondMappingCone f).hom
    (topologicalSecondMappingConeToSuspension_basepoint f)
    (topologicalSuspensionToSecondMappingCone_basepoint f)
  exact congrArg TopCat.Hom.hom
    (topologicalSuspensionToSecondMappingCone_toSuspension f)

/-- The explicit section of the second Puppe comparison is injective on every homotopy group. -/
theorem topologicalSuspensionToSecondMappingCone_homotopyGroup_injective
    (N : Type v) (f : A ⟶ X) :
    Function.Injective
      (HomotopyGroup.map (N := N)
        (topologicalSuspensionToSecondMappingCone f).hom
        (topologicalSuspensionToSecondMappingCone_basepoint f)) := by
  apply homotopyGroup_retraction_injective
    (topologicalSuspensionToSecondMappingCone f).hom
    (topologicalSecondMappingConeToSuspension f).hom
    (topologicalSuspensionToSecondMappingCone_basepoint f)
    (topologicalSecondMappingConeToSuspension_basepoint f)
  exact congrArg TopCat.Hom.hom
    (topologicalSuspensionToSecondMappingCone_toSuspension f)

end Submission
