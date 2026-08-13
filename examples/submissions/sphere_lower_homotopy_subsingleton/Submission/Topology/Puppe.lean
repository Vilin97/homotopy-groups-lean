/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.SuspensionComparison

/-!
# The first maps in the Puppe sequence

For a map `f : A ⟶ X`, the composite from its mapping cone through the cofiber collapse and
the suspension of `f`

`C_f ⟶ ΣA ⟶ ΣX`

is canonically nullhomotopic.  Point-set theoretically it factors through the contractible cone
on `X`: the original-space summand maps to the cone base, and the cone summand is carried by the
cone of `f`.

This is the first exactness component of the Puppe sequence.  It also shows directly that a
homotopy section of the cofiber collapse forces the suspended attaching map to be nullhomotopic.
-/

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory
  CartesianMonoidalCategory
open scoped Topology TopCat

noncomputable section

namespace Submission

universe u

/-- The canonical map from the mapping cone of `f` to the cone on its target. -/
def topologicalMappingConeToCone {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalMappingCone f ⟶ topologicalCone X :=
  pushout.desc (topologicalConeBaseIncl X) (topologicalConeMap f)
    (topologicalConeBaseIncl_map f).symm

@[reassoc (attr := simp)]
theorem topologicalMappingConeIncl_toCone {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalMappingConeIncl f ≫ topologicalMappingConeToCone f =
      topologicalConeBaseIncl X :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalMappingConeConeIncl_toCone {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalMappingConeConeIncl f ≫ topologicalMappingConeToCone f =
      topologicalConeMap f :=
  pushout.inr_desc _ _ _

/-- The first Puppe composite factors exactly through the cone on the target. -/
theorem topologicalMappingConeCollapse_suspensionMap {A X : TopCat.{u}}
    (f : A ⟶ X) :
    topologicalMappingConeCollapse f ≫ topologicalSuspensionMap A f =
      topologicalMappingConeToCone f ≫ topologicalSuspensionConeIncl X := by
  apply topologicalMappingCone_hom_ext f
  · simp
    exact topologicalMappingCone_condition (toUnit X)
  · simp

/-- The first Puppe composite contracts canonically through the cone on the target. -/
def topologicalMappingConeCollapseSuspensionNullhomotopy
    {A X : TopCat.{u}} (f : A ⟶ X) :
    TopCat.Homotopy
      (topologicalMappingConeCollapse f ≫ topologicalSuspensionMap A f)
      (toUnit (topologicalMappingCone f) ≫
        topologicalConePointIncl X ≫ topologicalSuspensionConeIncl X) := by
  let g := topologicalSuspensionConeIncl X
  let Hcone : TopCat.Homotopy g
      ((toUnit (topologicalCone X) ≫ topologicalConePointIncl X) ≫ g) :=
    (TopCat.Homotopy.refl g).comp (topologicalConeContractHomotopy X)
  have H := Hcone.comp
    (TopCat.Homotopy.refl (topologicalMappingConeToCone f))
  have hunit : topologicalMappingConeToCone f ≫ toUnit (topologicalCone X) =
      toUnit (topologicalMappingCone f) :=
    Subsingleton.elim _ _
  rw [← topologicalMappingConeCollapse_suspensionMap] at H
  have hend :
      topologicalMappingConeToCone f ≫
          ((toUnit (topologicalCone X) ≫ topologicalConePointIncl X) ≫ g) =
        toUnit (topologicalMappingCone f) ≫
          topologicalConePointIncl X ≫ g := by
    calc
      _ = (topologicalMappingConeToCone f ≫ toUnit (topologicalCone X)) ≫
          (topologicalConePointIncl X ≫ g) := by
        simp only [Category.assoc]
      _ = toUnit (topologicalMappingCone f) ≫
          (topologicalConePointIncl X ≫ g) := by rw [hunit]
      _ = _ := (Category.assoc _ _ _).symm
  exact H.cast rfl (congrArg TopCat.Hom.hom hend)

/-- The composite `C_f ⟶ ΣA ⟶ ΣX` is nullhomotopic. -/
theorem topologicalMappingConeCollapse_suspensionMap_nullhomotopic
    {A X : TopCat.{u}} (f : A ⟶ X) :
    (topologicalMappingConeCollapse f ≫
      topologicalSuspensionMap A f).hom.Nullhomotopic := by
  rw [topologicalMappingConeCollapse_suspensionMap]
  exact ((id_nullhomotopic (topologicalCone X)).comp_left
    (topologicalMappingConeToCone f).hom).comp_right
      (topologicalSuspensionConeIncl X).hom

/-- A homotopy section of the cofiber collapse forces the suspended attaching map to be
nullhomotopic. -/
theorem topologicalSuspensionMap_nullhomotopic_of_collapse_homotopy_section
    {A X : TopCat.{u}} (f : A ⟶ X)
    (s : topologicalSuspension A ⟶ topologicalMappingCone f)
    (Hs : TopCat.Homotopy
      (s ≫ topologicalMappingConeCollapse f)
        (𝟙 (topologicalSuspension A))) :
    (topologicalSuspensionMap A f).hom.Nullhomotopic := by
  let F := topologicalSuspensionMap A f
  have Hpost : TopCat.Homotopy
      ((s ≫ topologicalMappingConeCollapse f) ≫ F)
      ((𝟙 (topologicalSuspension A)) ≫ F) :=
    (TopCat.Homotopy.refl F).comp Hs
  have Hpost' : TopCat.Homotopy
      (s ≫ (topologicalMappingConeCollapse f ≫ F)) F := by
    simpa only [Category.assoc, Category.id_comp] using Hpost
  obtain ⟨z, hz⟩ :=
    (topologicalMappingConeCollapse_suspensionMap_nullhomotopic f).comp_left s.hom
  refine ⟨z, ?_⟩
  exact ⟨Hpost'.symm.trans hz.some⟩

end Submission
