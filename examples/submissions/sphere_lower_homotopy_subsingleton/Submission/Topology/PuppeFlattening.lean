/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.PuppeDeformation

/-!
# Flattening the normalized iterated mapping cone

After the first Puppe deformation has replaced the outer cone height by the maximum of the
inner and outer heights, the inner cone coordinate can be shrunk toward its base while that
maximum height is held fixed.  This file constructs the first quotient-compatible pieces of
that second deformation stage.
-/

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory
  CartesianMonoidalCategory
open scoped Topology TopCat

noncomputable section

namespace Submission

universe u

variable {A X : TopCat.{u}}

/-- On the double-cylinder piece, multiply the inner height by `1 - t` and retain the outer
maximum height `max v u`. -/
def topologicalSecondInnerHeightShrinkCylinderAt
    (f : A ⟶ X) (t v : TopCat.I) :
    A ⊗ TopCat.I ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  lift
      (lift (fst A TopCat.I)
          (lift (snd A TopCat.I) (TopCat.const t ≫ TopCat.I.symm) ≫
            TopCat.I.mul) ≫
        topologicalConeCylinderIncl A ≫ topologicalMappingConeConeIncl f)
      (lift (TopCat.const v) (snd A TopCat.I) ≫ TopCat.I.max) ≫
    topologicalConeCylinderIncl (topologicalMappingCone f) ≫
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)

@[simp]
theorem topologicalSecondInnerHeightShrinkCylinderAt_apply
    (f : A ⟶ X) (t v : TopCat.I) (a : A) (u : TopCat.I) :
    topologicalSecondInnerHeightShrinkCylinderAt f t v (a, u) =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeConeIncl f
              (topologicalConeCylinderIncl A
                (a, TopCat.I.mul (u, TopCat.I.symm t))),
            TopCat.I.max (v, u))) :=
  rfl

/-- The inner cone apex maps to the outer cone apex throughout the flattening. -/
def topologicalSecondInnerHeightShrinkPoint
    (f : A ⟶ X) :
    𝟙_ TopCat.{u} ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  topologicalConePointIncl (topologicalMappingCone f) ≫
    topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)

@[reassoc]
theorem topologicalSecondInnerHeightShrink_ι₁
    (f : A ⟶ X) (t v : TopCat.I) :
    TopCat.ι₁ ≫ topologicalSecondInnerHeightShrinkCylinderAt f t v =
      toUnit A ≫ topologicalSecondInnerHeightShrinkPoint f := by
  apply TopCat.hom_ext
  ext a
  change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
      (topologicalConeCylinderIncl (topologicalMappingCone f)
        (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A
              (a, TopCat.I.mul (1, TopCat.I.symm t))),
          TopCat.I.max (v, 1))) =
    topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
      (topologicalConePointIncl (topologicalMappingCone f) (toUnit A a))
  rw [TopCat.I.max_one_right]
  exact congrArg
    (topologicalMappingConeConeIncl (topologicalMappingConeCollapse f))
    (ConcreteCategory.congr_hom (pushout.condition :
      (TopCat.ι₁ : topologicalMappingCone f ⟶
          topologicalMappingCone f ⊗ TopCat.I) ≫
            topologicalConeCylinderIncl (topologicalMappingCone f) =
        toUnit (topologicalMappingCone f) ≫
          topologicalConePointIncl (topologicalMappingCone f))
      (topologicalMappingConeConeIncl f
        (topologicalConeCylinderIncl A
          (a, TopCat.I.mul (1, TopCat.I.symm t)))))

/-- The inner-cone part of the second-stage flattening at fixed time and outer height. -/
def topologicalSecondInnerHeightShrinkConeAt
    (f : A ⟶ X) (t v : TopCat.I) :
    topologicalCone A ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  topologicalConeDesc A
    (topologicalSecondInnerHeightShrinkCylinderAt f t v)
    (topologicalSecondInnerHeightShrinkPoint f)
    (topologicalSecondInnerHeightShrink_ι₁ f t v)

@[reassoc (attr := simp)]
theorem topologicalConeCylinderIncl_secondInnerHeightShrinkConeAt
    (f : A ⟶ X) (t v : TopCat.I) :
    topologicalConeCylinderIncl A ≫
        topologicalSecondInnerHeightShrinkConeAt f t v =
      topologicalSecondInnerHeightShrinkCylinderAt f t v :=
  topologicalConeCylinderIncl_desc _ _ _ _

@[reassoc (attr := simp)]
theorem topologicalConePointIncl_secondInnerHeightShrinkConeAt
    (f : A ⟶ X) (t v : TopCat.I) :
    topologicalConePointIncl A ≫
        topologicalSecondInnerHeightShrinkConeAt f t v =
      topologicalSecondInnerHeightShrinkPoint f :=
  topologicalConePointIncl_desc _ _ _ _

/-- On the original-space summand of `C_f`, retain the outer cylinder point and its height. -/
def topologicalSecondOriginalHeightShrinkAt
    (f : A ⟶ X) (v : TopCat.I) :
    X ⟶ topologicalMappingCone (topologicalMappingConeCollapse f) :=
  lift (topologicalMappingConeIncl f) (TopCat.const v) ≫
    topologicalConeCylinderIncl (topologicalMappingCone f) ≫
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)

@[reassoc]
theorem topologicalSecondInnerHeightShrink_base
    (f : A ⟶ X) (t v : TopCat.I) :
    f ≫ topologicalSecondOriginalHeightShrinkAt f v =
      topologicalConeBaseIncl A ≫
        topologicalSecondInnerHeightShrinkConeAt f t v := by
  apply TopCat.hom_ext
  ext a
  have hcylinder := ConcreteCategory.congr_hom
    (topologicalConeCylinderIncl_secondInnerHeightShrinkConeAt f t v)
    (a, (0 : TopCat.I.{u}))
  change topologicalSecondInnerHeightShrinkConeAt f t v
      (topologicalConeBaseIncl A a) =
    topologicalSecondInnerHeightShrinkCylinderAt f t v (a, 0) at hcylinder
  change topologicalSecondOriginalHeightShrinkAt f v (f a) =
    topologicalSecondInnerHeightShrinkConeAt f t v
      (topologicalConeBaseIncl A a)
  rw [hcylinder]
  change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
      (topologicalConeCylinderIncl (topologicalMappingCone f)
        (topologicalMappingConeIncl f (f a), v)) =
    topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
      (topologicalConeCylinderIncl (topologicalMappingCone f)
        (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A
              (a, TopCat.I.mul (0, TopCat.I.symm t))),
          TopCat.I.max (v, 0)))
  rw [TopCat.I.mul_zero_left, TopCat.I.max_zero_right]
  have hinner := ConcreteCategory.congr_hom
    (topologicalMappingCone_condition f) a
  change topologicalMappingConeIncl f (f a) =
    topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A (a, 0)) at hinner
  rw [hinner]

/-- At fixed outer height, the second-stage formula descends from the original-space and inner
cone pieces to the whole first mapping cone. -/
def topologicalSecondMappingConeHeightShrinkAt
    (f : A ⟶ X) (t v : TopCat.I) :
    topologicalMappingCone f ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  pushout.desc
    (topologicalSecondOriginalHeightShrinkAt f v)
    (topologicalSecondInnerHeightShrinkConeAt f t v)
    (topologicalSecondInnerHeightShrink_base f t v)

@[reassoc (attr := simp)]
theorem topologicalMappingConeIncl_secondHeightShrinkAt
    (f : A ⟶ X) (t v : TopCat.I) :
    topologicalMappingConeIncl f ≫
        topologicalSecondMappingConeHeightShrinkAt f t v =
      topologicalSecondOriginalHeightShrinkAt f v :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalMappingConeConeIncl_secondHeightShrinkAt
    (f : A ⟶ X) (t v : TopCat.I) :
    topologicalMappingConeConeIncl f ≫
        topologicalSecondMappingConeHeightShrinkAt f t v =
      topologicalSecondInnerHeightShrinkConeAt f t v :=
  pushout.inr_desc _ _ _

end Submission
