/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Topology.Homotopy.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Topological cones and mapping cones

The cone on `A` is the pushout which collapses the `1`-end of `A × I` to a point.  The mapping
cone of `f : A ⟶ X` is the pushout which glues the remaining `0`-end of that cone to `X` by
`f`.  The categorical definitions make the key nullhomotopy argument formal: a nullhomotopy of
`f` extends over the cone and therefore gives a retraction of the mapping-cone inclusion
`X ⟶ C_f`.

## Main definitions and results

* `Submission.topologicalCone A` and `Submission.topologicalConeBaseIncl A`;
* `Submission.topologicalMappingCone f` and `Submission.topologicalMappingConeIncl f`;
* `Submission.topologicalConeExtensionOfNullhomotopy`;
* `Submission.topologicalMappingConeRetractOfNullhomotopy`.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

noncomputable section

namespace Submission

universe u

/-- The topological cone on `A`, obtained by collapsing `A × {1}` to a point. -/
def topologicalCone (A : TopCat.{u}) : TopCat.{u} :=
  pushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) (toUnit A)

/-- The quotient map from the cylinder into the cone. -/
def topologicalConeCylinderIncl (A : TopCat.{u}) : A ⊗ TopCat.I ⟶ topologicalCone A :=
  pushout.inl (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) (toUnit A)

/-- The cone point. -/
def topologicalConePointIncl (A : TopCat.{u}) :
    𝟙_ TopCat.{u} ⟶ topologicalCone A :=
  pushout.inr (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) (toUnit A)

/-- The inclusion of the base `A × {0}` into the cone. -/
def topologicalConeBaseIncl (A : TopCat.{u}) : A ⟶ topologicalCone A :=
  TopCat.ι₀ ≫ topologicalConeCylinderIncl A

/-- Define a map out of the cone from a map on the cylinder whose `1`-end is constant. -/
def topologicalConeDesc (A : TopCat.{u}) {Y : TopCat.{u}}
    (F : A ⊗ TopCat.I ⟶ Y) (y : 𝟙_ TopCat.{u} ⟶ Y)
    (h : TopCat.ι₁ ≫ F = toUnit A ≫ y) : topologicalCone A ⟶ Y :=
  pushout.desc F y h

@[reassoc (attr := simp)]
theorem topologicalConeCylinderIncl_desc (A : TopCat.{u}) {Y : TopCat.{u}}
    (F : A ⊗ TopCat.I ⟶ Y) (y : 𝟙_ TopCat.{u} ⟶ Y)
    (h : TopCat.ι₁ ≫ F = toUnit A ≫ y) :
    topologicalConeCylinderIncl A ≫ topologicalConeDesc A F y h = F :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalConePointIncl_desc (A : TopCat.{u}) {Y : TopCat.{u}}
    (F : A ⊗ TopCat.I ⟶ Y) (y : 𝟙_ TopCat.{u} ⟶ Y)
    (h : TopCat.ι₁ ≫ F = toUnit A ≫ y) :
    topologicalConePointIncl A ≫ topologicalConeDesc A F y h = y :=
  pushout.inr_desc _ _ _

/-- A nullhomotopy of `f` extends `f` over the topological cone. -/
def topologicalConeExtensionOfNullhomotopy {A X : TopCat.{u}} (f : A ⟶ X)
    (x : 𝟙_ TopCat.{u} ⟶ X) (H : TopCat.Homotopy f (toUnit A ≫ x)) :
    topologicalCone A ⟶ X :=
  topologicalConeDesc A H.h x H.ι₁_h

/-- The cone extension restricts to the original map on the base. -/
@[reassoc (attr := simp)]
theorem topologicalConeBaseIncl_extensionOfNullhomotopy
    {A X : TopCat.{u}} (f : A ⟶ X) (x : 𝟙_ TopCat.{u} ⟶ X)
    (H : TopCat.Homotopy f (toUnit A ≫ x)) :
    topologicalConeBaseIncl A ≫ topologicalConeExtensionOfNullhomotopy f x H = f := by
  rw [topologicalConeBaseIncl, Category.assoc,
    topologicalConeExtensionOfNullhomotopy, topologicalConeCylinderIncl_desc, H.ι₀_h]

/-- The topological mapping cone of `f : A ⟶ X`. -/
def topologicalMappingCone {A X : TopCat.{u}} (f : A ⟶ X) : TopCat.{u} :=
  pushout f (topologicalConeBaseIncl A)

/-- The canonical inclusion `X ⟶ C_f`. -/
def topologicalMappingConeIncl {A X : TopCat.{u}} (f : A ⟶ X) :
    X ⟶ topologicalMappingCone f :=
  pushout.inl f (topologicalConeBaseIncl A)

/-- The canonical map from the cone into `C_f`. -/
def topologicalMappingConeConeIncl {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalCone A ⟶ topologicalMappingCone f :=
  pushout.inr f (topologicalConeBaseIncl A)

/-- The defining square of the mapping cone commutes. -/
@[reassoc]
theorem topologicalMappingCone_condition {A X : TopCat.{u}} (f : A ⟶ X) :
    f ≫ topologicalMappingConeIncl f =
      topologicalConeBaseIncl A ≫ topologicalMappingConeConeIncl f :=
  pushout.condition

/-- A nullhomotopy of `f` produces a retraction from its mapping cone to `X`. -/
def topologicalMappingConeRetractOfNullhomotopy {A X : TopCat.{u}} (f : A ⟶ X)
    (x : 𝟙_ TopCat.{u} ⟶ X) (H : TopCat.Homotopy f (toUnit A ≫ x)) :
    topologicalMappingCone f ⟶ X :=
  pushout.desc (𝟙 X) (topologicalConeExtensionOfNullhomotopy f x H) (by
    rw [Category.comp_id, topologicalConeBaseIncl_extensionOfNullhomotopy])

/-- The map produced by a nullhomotopy retracts the mapping-cone inclusion. -/
@[reassoc (attr := simp)]
theorem topologicalMappingConeIncl_retractOfNullhomotopy
    {A X : TopCat.{u}} (f : A ⟶ X) (x : 𝟙_ TopCat.{u} ⟶ X)
    (H : TopCat.Homotopy f (toUnit A ≫ x)) :
    topologicalMappingConeIncl f ≫
      topologicalMappingConeRetractOfNullhomotopy f x H = 𝟙 X := by
  unfold topologicalMappingConeIncl topologicalMappingConeRetractOfNullhomotopy
  exact pushout.inl_desc _ _ _

end Submission
