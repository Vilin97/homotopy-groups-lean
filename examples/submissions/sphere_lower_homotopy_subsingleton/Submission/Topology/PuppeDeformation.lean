/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.PuppeComparison

/-!
# Deforming the iterated mapping cone

This file begins the deformation of the mapping cone of `C_f -> Sigma A` toward the image of
the canonical section from `Sigma X`.  On the outer cone over `C_f`, the first normalization
raises the outer cone coordinate by `t` times the inner mapping-cone height.  The formula is
compatible with both cone apex identifications and varies continuously in `t`.
-/

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory
  CartesianMonoidalCategory
open scoped Topology TopCat

noncomputable section

namespace Submission

universe u

variable {A X : TopCat.{u}}

/-- Move the cone-cylinder part of the bottom suspension into the outer cone.  At time `t`,
the point represented by `(a, u)` acquires outer height `u * t`, while its inner cone height
remains `u`. -/
def topologicalSecondBottomConeCylinderHeightRaiseAt (f : A ⟶ X) (t : TopCat.I) :
    A ⊗ TopCat.I ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  lift
      (topologicalConeCylinderIncl A ≫ topologicalMappingConeConeIncl f)
      (lift (snd A TopCat.I) (TopCat.const t) ≫ TopCat.I.mul) ≫
    topologicalConeCylinderIncl (topologicalMappingCone f) ≫
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)

@[simp]
theorem topologicalSecondBottomConeCylinderHeightRaiseAt_apply
    (f : A ⟶ X) (t : TopCat.I) (a : A) (u : TopCat.I) :
    topologicalSecondBottomConeCylinderHeightRaiseAt f t (a, u) =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A (a, u)), TopCat.I.mul (u, t))) :=
  rfl

/-- The image of the cone apex under the bottom-suspension deformation. -/
def topologicalSecondBottomConePointHeightRaiseAt (f : A ⟶ X) (t : TopCat.I) :
    𝟙_ TopCat.{u} ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  lift
      (topologicalConePointIncl A ≫ topologicalMappingConeConeIncl f)
      (TopCat.const t) ≫
    topologicalConeCylinderIncl (topologicalMappingCone f) ≫
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)

@[simp]
theorem topologicalSecondBottomConePointHeightRaiseAt_apply
    (f : A ⟶ X) (t : TopCat.I) (z : 𝟙_ TopCat.{u}) :
    topologicalSecondBottomConePointHeightRaiseAt f t z =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z), t)) :=
  rfl

@[reassoc]
theorem topologicalSecondBottomCone_ι₁_heightRaiseAt
    (f : A ⟶ X) (t : TopCat.I) :
    TopCat.ι₁ ≫ topologicalSecondBottomConeCylinderHeightRaiseAt f t =
      toUnit A ≫ topologicalSecondBottomConePointHeightRaiseAt f t := by
  apply TopCat.hom_ext
  ext a
  change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
      (topologicalConeCylinderIncl (topologicalMappingCone f)
        (topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A (a, 1)), TopCat.I.mul (1, t))) =
    topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
      (topologicalConeCylinderIncl (topologicalMappingCone f)
        (topologicalMappingConeConeIncl f
          (topologicalConePointIncl A (toUnit A a)), t))
  rw [TopCat.I.mul_one_left]
  have hapex := ConcreteCategory.congr_hom (pushout.condition :
    (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) ≫ topologicalConeCylinderIncl A =
      toUnit A ≫ topologicalConePointIncl A) a
  change topologicalConeCylinderIncl A (a, 1) =
    topologicalConePointIncl A (toUnit A a) at hapex
  rw [hapex]

/-- The cone part of the bottom suspension moves continuously into the outer cone, with outer
height proportional to the original suspension coordinate. -/
def topologicalSecondBottomConeHeightRaiseAt (f : A ⟶ X) (t : TopCat.I) :
    topologicalCone A ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  topologicalConeDesc A
    (topologicalSecondBottomConeCylinderHeightRaiseAt f t)
    (topologicalSecondBottomConePointHeightRaiseAt f t)
    (topologicalSecondBottomCone_ι₁_heightRaiseAt f t)

@[reassoc (attr := simp)]
theorem topologicalSecondBottomConeCylinderIncl_heightRaiseAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalConeCylinderIncl A ≫
        topologicalSecondBottomConeHeightRaiseAt f t =
      topologicalSecondBottomConeCylinderHeightRaiseAt f t :=
  topologicalConeCylinderIncl_desc _ _ _ _

@[reassoc (attr := simp)]
theorem topologicalSecondBottomConePointIncl_heightRaiseAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalConePointIncl A ≫
        topologicalSecondBottomConeHeightRaiseAt f t =
      topologicalSecondBottomConePointHeightRaiseAt f t :=
  topologicalConePointIncl_desc _ _ _ _

@[reassoc]
theorem topologicalSecondBottomConeBaseIncl_heightRaiseAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalConeBaseIncl A ≫
        topologicalSecondBottomConeHeightRaiseAt f t =
      toUnit A ≫ topologicalSuspensionPointIncl A ≫
        topologicalMappingConeIncl (topologicalMappingConeCollapse f) := by
  apply TopCat.hom_ext
  ext a
  have hcylinder := ConcreteCategory.congr_hom
    (topologicalSecondBottomConeCylinderIncl_heightRaiseAt f t)
    (a, (0 : TopCat.I.{u}))
  change topologicalSecondBottomConeHeightRaiseAt f t
      (topologicalConeBaseIncl A a) =
    topologicalSecondBottomConeCylinderHeightRaiseAt f t (a, 0) at hcylinder
  change topologicalSecondBottomConeHeightRaiseAt f t
      (topologicalConeBaseIncl A a) =
    topologicalMappingConeIncl (topologicalMappingConeCollapse f)
      (topologicalSuspensionPointIncl A (toUnit A a))
  rw [hcylinder]
  change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
      (topologicalConeCylinderIncl (topologicalMappingCone f)
        (topologicalMappingConeConeIncl f (topologicalConeBaseIncl A a),
          TopCat.I.mul (0, t))) =
    topologicalMappingConeIncl (topologicalMappingConeCollapse f)
      (topologicalSuspensionPointIncl A (toUnit A a))
  rw [TopCat.I.mul_zero_left]
  have hinner := ConcreteCategory.congr_hom
    (topologicalMappingCone_condition f) a
  change topologicalMappingConeIncl f (f a) =
    topologicalMappingConeConeIncl f (topologicalConeBaseIncl A a) at hinner
  rw [← hinner]
  have houter := ConcreteCategory.congr_hom
    (topologicalMappingCone_condition (topologicalMappingConeCollapse f))
    (topologicalMappingConeIncl f (f a))
  change topologicalMappingConeIncl (topologicalMappingConeCollapse f)
      (topologicalMappingConeCollapse f (topologicalMappingConeIncl f (f a))) =
    topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
      (topologicalConeCylinderIncl (topologicalMappingCone f)
        (topologicalMappingConeIncl f (f a), 0)) at houter
  rw [← houter]
  have hcollapse := ConcreteCategory.congr_hom
    (topologicalMappingConeIncl_collapse f) (f a)
  change topologicalMappingConeCollapse f (topologicalMappingConeIncl f (f a)) =
    topologicalSuspensionPointIncl A (toUnit X (f a)) at hcollapse
  rw [hcollapse]
  rfl

/-- The bottom suspension map forced by the outer-cone height normalization.  Its distinguished
point stays in the bottom summand, while a cone point of height `u` moves to outer height
`u * t`. -/
def topologicalSecondBottomHeightRaiseAt (f : A ⟶ X) (t : TopCat.I) :
    topologicalSuspension A ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  pushout.desc
    (topologicalSuspensionPointIncl A ≫
      topologicalMappingConeIncl (topologicalMappingConeCollapse f))
    (topologicalSecondBottomConeHeightRaiseAt f t)
    (topologicalSecondBottomConeBaseIncl_heightRaiseAt f t).symm

@[reassoc (attr := simp)]
theorem topologicalSuspensionPointIncl_secondBottomHeightRaiseAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalSuspensionPointIncl A ≫
        topologicalSecondBottomHeightRaiseAt f t =
      topologicalSuspensionPointIncl A ≫
        topologicalMappingConeIncl (topologicalMappingConeCollapse f) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalSuspensionConeIncl_secondBottomHeightRaiseAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalSuspensionConeIncl A ≫
        topologicalSecondBottomHeightRaiseAt f t =
      topologicalSecondBottomConeHeightRaiseAt f t :=
  pushout.inr_desc _ _ _

@[simp]
theorem topologicalSecondBottomHeightRaiseAt_point
    (f : A ⟶ X) (t : TopCat.I) (z : 𝟙_ TopCat.{u}) :
    topologicalSecondBottomHeightRaiseAt f t
        (topologicalSuspensionPointIncl A z) =
      topologicalMappingConeIncl (topologicalMappingConeCollapse f)
        (topologicalSuspensionPointIncl A z) := by
  exact ConcreteCategory.congr_hom
    (topologicalSuspensionPointIncl_secondBottomHeightRaiseAt f t) z

@[simp]
theorem topologicalSecondBottomHeightRaiseAt_cylinder
    (f : A ⟶ X) (t : TopCat.I) (a : A) (u : TopCat.I) :
    topologicalSecondBottomHeightRaiseAt f t
        (topologicalSuspensionConeIncl A
          (topologicalConeCylinderIncl A (a, u))) =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A (a, u)), TopCat.I.mul (u, t))) := by
  rw [show topologicalSecondBottomHeightRaiseAt f t
      (topologicalSuspensionConeIncl A
        (topologicalConeCylinderIncl A (a, u))) =
    topologicalSecondBottomConeHeightRaiseAt f t
      (topologicalConeCylinderIncl A (a, u)) from
        ConcreteCategory.congr_hom
          (topologicalSuspensionConeIncl_secondBottomHeightRaiseAt f t)
          (topologicalConeCylinderIncl A (a, u))]
  exact ConcreteCategory.congr_hom
    (topologicalSecondBottomConeCylinderIncl_heightRaiseAt f t) (a, u)

@[simp]
theorem topologicalSecondBottomHeightRaiseAt_apex
    (f : A ⟶ X) (t : TopCat.I) (z : 𝟙_ TopCat.{u}) :
    topologicalSecondBottomHeightRaiseAt f t
        (topologicalSuspensionConeIncl A (topologicalConePointIncl A z)) =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z), t)) := by
  rw [show topologicalSecondBottomHeightRaiseAt f t
      (topologicalSuspensionConeIncl A (topologicalConePointIncl A z)) =
    topologicalSecondBottomConeHeightRaiseAt f t
      (topologicalConePointIncl A z) from
        ConcreteCategory.congr_hom
          (topologicalSuspensionConeIncl_secondBottomHeightRaiseAt f t)
          (topologicalConePointIncl A z)]
  exact ConcreteCategory.congr_hom
    (topologicalSecondBottomConePointIncl_heightRaiseAt f t) z

/-- On the cylinder of the outer cone, keep the source point and replace its outer height `v`
by `max v (t * height(c))`. -/
def topologicalSecondConeHeightRaiseCylinderAt (f : A ⟶ X) (t : TopCat.I) :
    topologicalMappingCone f ⊗ TopCat.I ⟶
      topologicalMappingCone f ⊗ TopCat.I :=
  lift (fst (topologicalMappingCone f) TopCat.I)
    (lift (snd (topologicalMappingCone f) TopCat.I)
      (lift
          (fst (topologicalMappingCone f) TopCat.I ≫
            topologicalMappingConeHeight f)
          (TopCat.const t) ≫ TopCat.I.mul) ≫
        TopCat.I.max)

@[simp]
theorem topologicalSecondConeHeightRaiseCylinderAt_apply
    (f : A ⟶ X) (t : TopCat.I) (c : topologicalMappingCone f) (v : TopCat.I) :
    topologicalSecondConeHeightRaiseCylinderAt f t (c, v) =
      (c, TopCat.I.max (v, TopCat.I.mul (topologicalMappingConeHeight f c, t))) :=
  rfl

@[simp]
theorem topologicalSecondConeHeightRaiseCylinderAt_zero (f : A ⟶ X) :
    topologicalSecondConeHeightRaiseCylinderAt f 0 =
      𝟙 (topologicalMappingCone f ⊗ TopCat.I) := by
  apply TopCat.hom_ext
  ext p
  rcases p with ⟨c, v⟩
  simp

/-- The time-`t` height normalization on the outer cone over `C_f`. -/
def topologicalSecondConeHeightRaiseAt (f : A ⟶ X) (t : TopCat.I) :
    topologicalCone (topologicalMappingCone f) ⟶
      topologicalCone (topologicalMappingCone f) :=
  topologicalConeDesc (topologicalMappingCone f)
    (topologicalSecondConeHeightRaiseCylinderAt f t ≫
      topologicalConeCylinderIncl (topologicalMappingCone f))
    (topologicalConePointIncl (topologicalMappingCone f)) (by
      apply TopCat.hom_ext
      ext c
      change topologicalConeCylinderIncl (topologicalMappingCone f)
          (c, TopCat.I.max (1,
            TopCat.I.mul (topologicalMappingConeHeight f c, t))) =
        topologicalConePointIncl (topologicalMappingCone f) PUnit.unit
      rw [TopCat.I.max_one_left]
      exact ConcreteCategory.congr_hom (pushout.condition :
        (TopCat.ι₁ : topologicalMappingCone f ⟶
            topologicalMappingCone f ⊗ TopCat.I) ≫
              topologicalConeCylinderIncl (topologicalMappingCone f) =
          toUnit (topologicalMappingCone f) ≫
            topologicalConePointIncl (topologicalMappingCone f)) c)

@[reassoc (attr := simp)]
theorem topologicalSecondConeCylinderIncl_heightRaiseAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalConeCylinderIncl (topologicalMappingCone f) ≫
        topologicalSecondConeHeightRaiseAt f t =
      topologicalSecondConeHeightRaiseCylinderAt f t ≫
        topologicalConeCylinderIncl (topologicalMappingCone f) :=
  topologicalConeCylinderIncl_desc _ _ _ _

@[reassoc (attr := simp)]
theorem topologicalSecondConePointIncl_heightRaiseAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalConePointIncl (topologicalMappingCone f) ≫
        topologicalSecondConeHeightRaiseAt f t =
      topologicalConePointIncl (topologicalMappingCone f) :=
  topologicalConePointIncl_desc _ _ _ _

@[simp]
theorem topologicalSecondConeHeightRaiseAt_cylinder
    (f : A ⟶ X) (t : TopCat.I) (c : topologicalMappingCone f) (v : TopCat.I) :
    topologicalSecondConeHeightRaiseAt f t
        (topologicalConeCylinderIncl (topologicalMappingCone f) (c, v)) =
      topologicalConeCylinderIncl (topologicalMappingCone f)
        (c, TopCat.I.max
          (v, TopCat.I.mul (topologicalMappingConeHeight f c, t))) := by
  rw [show topologicalSecondConeHeightRaiseAt f t
      (topologicalConeCylinderIncl (topologicalMappingCone f) (c, v)) =
    topologicalConeCylinderIncl (topologicalMappingCone f)
      (topologicalSecondConeHeightRaiseCylinderAt f t (c, v)) from
        ConcreteCategory.congr_hom
          (topologicalSecondConeCylinderIncl_heightRaiseAt f t) (c, v)]
  rfl

@[simp]
theorem topologicalSecondConeHeightRaiseAt_base
    (f : A ⟶ X) (t : TopCat.I) (c : topologicalMappingCone f) :
    topologicalSecondConeHeightRaiseAt f t
        (topologicalConeBaseIncl (topologicalMappingCone f) c) =
      topologicalConeCylinderIncl (topologicalMappingCone f)
        (c, TopCat.I.mul (topologicalMappingConeHeight f c, t)) := by
  rw [show topologicalConeBaseIncl (topologicalMappingCone f) c =
    topologicalConeCylinderIncl (topologicalMappingCone f) (c, 0) from rfl]
  rw [topologicalSecondConeHeightRaiseAt_cylinder, TopCat.I.max_zero_left]

/-- The bottom-suspension deformation and the outer-cone deformation agree on their common
copy of `C_f`; hence they glue to a self-map of the second mapping cone. -/
@[reassoc]
theorem topologicalSecondHeightRaiseAt_condition
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalMappingConeCollapse f ≫
        topologicalSecondBottomHeightRaiseAt f t =
      topologicalConeBaseIncl (topologicalMappingCone f) ≫
        topologicalSecondConeHeightRaiseAt f t ≫
          topologicalMappingConeConeIncl (topologicalMappingConeCollapse f) := by
  apply topologicalMappingCone_hom_ext f
  · apply TopCat.hom_ext
    ext x
    change topologicalSecondBottomHeightRaiseAt f t
        (topologicalMappingConeCollapse f (topologicalMappingConeIncl f x)) =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalSecondConeHeightRaiseAt f t
          (topologicalConeBaseIncl (topologicalMappingCone f)
            (topologicalMappingConeIncl f x)))
    have hcollapse := ConcreteCategory.congr_hom
      (topologicalMappingConeIncl_collapse f) x
    change topologicalMappingConeCollapse f (topologicalMappingConeIncl f x) =
      topologicalSuspensionPointIncl A (toUnit X x) at hcollapse
    rw [hcollapse, topologicalSecondBottomHeightRaiseAt_point,
      topologicalSecondConeHeightRaiseAt_base]
    have hheight := ConcreteCategory.congr_hom
      (topologicalMappingConeIncl_height f) x
    change topologicalMappingConeHeight f (topologicalMappingConeIncl f x) = 0 at hheight
    rw [hheight, TopCat.I.mul_zero_left]
    have houter := ConcreteCategory.congr_hom
      (topologicalMappingCone_condition (topologicalMappingConeCollapse f))
      (topologicalMappingConeIncl f x)
    change topologicalMappingConeIncl (topologicalMappingConeCollapse f)
        (topologicalMappingConeCollapse f (topologicalMappingConeIncl f x)) =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeIncl f x, 0)) at houter
    rw [← houter, hcollapse]
  · apply topologicalCone_hom_ext A
    · apply TopCat.hom_ext
      ext p
      rcases p with ⟨a, u⟩
      change topologicalSecondBottomHeightRaiseAt f t
          (topologicalMappingConeCollapse f
            (topologicalMappingConeConeIncl f
              (topologicalConeCylinderIncl A (a, u)))) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalSecondConeHeightRaiseAt f t
            (topologicalConeBaseIncl (topologicalMappingCone f)
              (topologicalMappingConeConeIncl f
                (topologicalConeCylinderIncl A (a, u)))))
      have hcollapse := ConcreteCategory.congr_hom
        (topologicalMappingConeConeIncl_collapse f)
        (topologicalConeCylinderIncl A (a, u))
      change topologicalMappingConeCollapse f
          (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A (a, u))) =
        topologicalSuspensionConeIncl A
          (topologicalConeCylinderIncl A (a, u)) at hcollapse
      rw [hcollapse, topologicalSecondBottomHeightRaiseAt_cylinder,
        topologicalSecondConeHeightRaiseAt_base]
      have hheight := ConcreteCategory.congr_hom
        (topologicalMappingConeConeIncl_height f)
        (topologicalConeCylinderIncl A (a, u))
      change topologicalMappingConeHeight f
          (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A (a, u))) =
        topologicalConeHeight A (topologicalConeCylinderIncl A (a, u)) at hheight
      rw [hheight]
      have hcone := ConcreteCategory.congr_hom
        (topologicalConeCylinderIncl_height A) (a, u)
      change topologicalConeHeight A (topologicalConeCylinderIncl A (a, u)) = u at hcone
      rw [hcone]
    · apply TopCat.hom_ext
      ext z
      change topologicalSecondBottomHeightRaiseAt f t
          (topologicalMappingConeCollapse f
            (topologicalMappingConeConeIncl f (topologicalConePointIncl A z))) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalSecondConeHeightRaiseAt f t
            (topologicalConeBaseIncl (topologicalMappingCone f)
              (topologicalMappingConeConeIncl f (topologicalConePointIncl A z))))
      have hcollapse := ConcreteCategory.congr_hom
        (topologicalMappingConeConeIncl_collapse f) (topologicalConePointIncl A z)
      change topologicalMappingConeCollapse f
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
        topologicalSuspensionConeIncl A (topologicalConePointIncl A z) at hcollapse
      rw [hcollapse, topologicalSecondBottomHeightRaiseAt_apex,
        topologicalSecondConeHeightRaiseAt_base]
      have hheight := ConcreteCategory.congr_hom
        (topologicalMappingConeConeIncl_height f) (topologicalConePointIncl A z)
      change topologicalMappingConeHeight f
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
        topologicalConeHeight A (topologicalConePointIncl A z) at hheight
      rw [hheight]
      have hcone := ConcreteCategory.congr_hom
        (topologicalConePointIncl_height A) z
      change topologicalConeHeight A (topologicalConePointIncl A z) = 1 at hcone
      rw [hcone, TopCat.I.mul_one_left]

/-- The quotient-compatible height normalization on the entire second mapping cone. -/
def topologicalSecondHeightRaiseAt (f : A ⟶ X) (t : TopCat.I) :
    topologicalMappingCone (topologicalMappingConeCollapse f) ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  pushout.desc
    (topologicalSecondBottomHeightRaiseAt f t)
    (topologicalSecondConeHeightRaiseAt f t ≫
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f))
    (topologicalSecondHeightRaiseAt_condition f t)

@[reassoc (attr := simp)]
theorem topologicalSecondMappingConeIncl_heightRaiseAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalMappingConeIncl (topologicalMappingConeCollapse f) ≫
        topologicalSecondHeightRaiseAt f t =
      topologicalSecondBottomHeightRaiseAt f t :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalSecondMappingConeConeIncl_heightRaiseAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalMappingConeConeIncl (topologicalMappingConeCollapse f) ≫
        topologicalSecondHeightRaiseAt f t =
      topologicalSecondConeHeightRaiseAt f t ≫
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f) :=
  pushout.inr_desc _ _ _

@[simp]
theorem topologicalSecondConeHeightRaiseAt_zero (f : A ⟶ X) :
    topologicalSecondConeHeightRaiseAt f 0 =
      𝟙 (topologicalCone (topologicalMappingCone f)) := by
  apply topologicalCone_hom_ext (topologicalMappingCone f)
  · rw [topologicalSecondConeCylinderIncl_heightRaiseAt,
      topologicalSecondConeHeightRaiseCylinderAt_zero,
      Category.id_comp, Category.comp_id]
  · rw [topologicalSecondConePointIncl_heightRaiseAt, Category.comp_id]

@[simp]
theorem topologicalSecondBottomHeightRaiseAt_zero (f : A ⟶ X) :
    topologicalSecondBottomHeightRaiseAt f 0 =
      topologicalMappingConeIncl (topologicalMappingConeCollapse f) := by
  apply topologicalMappingCone_hom_ext (toUnit A)
  · simpa only [topologicalSuspensionPointIncl, topologicalSuspension] using
      topologicalSuspensionPointIncl_secondBottomHeightRaiseAt f 0
  · apply topologicalCone_hom_ext A
    · apply TopCat.hom_ext
      ext p
      rcases p with ⟨a, u⟩
      change topologicalSecondBottomHeightRaiseAt f 0
          (topologicalSuspensionConeIncl A
            (topologicalConeCylinderIncl A (a, u))) =
        topologicalMappingConeIncl (topologicalMappingConeCollapse f)
          (topologicalSuspensionConeIncl A
            (topologicalConeCylinderIncl A (a, u)))
      rw [topologicalSecondBottomHeightRaiseAt_cylinder,
        TopCat.I.mul_zero_right]
      let c : topologicalMappingCone f :=
        topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A (a, u))
      have houter := ConcreteCategory.congr_hom
        (topologicalMappingCone_condition (topologicalMappingConeCollapse f)) c
      change topologicalMappingConeIncl (topologicalMappingConeCollapse f)
          (topologicalMappingConeCollapse f c) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeCylinderIncl (topologicalMappingCone f) (c, 0)) at houter
      rw [← houter]
      have hcollapse := ConcreteCategory.congr_hom
        (topologicalMappingConeConeIncl_collapse f)
        (topologicalConeCylinderIncl A (a, u))
      change topologicalMappingConeCollapse f c =
        topologicalSuspensionConeIncl A
          (topologicalConeCylinderIncl A (a, u)) at hcollapse
      rw [hcollapse]
    · apply TopCat.hom_ext
      ext z
      change topologicalSecondBottomHeightRaiseAt f 0
          (topologicalSuspensionConeIncl A (topologicalConePointIncl A z)) =
        topologicalMappingConeIncl (topologicalMappingConeCollapse f)
          (topologicalSuspensionConeIncl A (topologicalConePointIncl A z))
      rw [topologicalSecondBottomHeightRaiseAt_apex]
      let c : topologicalMappingCone f :=
        topologicalMappingConeConeIncl f (topologicalConePointIncl A z)
      have houter := ConcreteCategory.congr_hom
        (topologicalMappingCone_condition (topologicalMappingConeCollapse f)) c
      change topologicalMappingConeIncl (topologicalMappingConeCollapse f)
          (topologicalMappingConeCollapse f c) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeCylinderIncl (topologicalMappingCone f) (c, 0)) at houter
      rw [← houter]
      have hcollapse := ConcreteCategory.congr_hom
        (topologicalMappingConeConeIncl_collapse f) (topologicalConePointIncl A z)
      change topologicalMappingConeCollapse f c =
        topologicalSuspensionConeIncl A (topologicalConePointIncl A z) at hcollapse
      rw [hcollapse]

/-- The bottom-suspension part of the height normalization is jointly continuous in time and
the suspension variable. -/
theorem continuous_topologicalSecondBottomHeightRaiseAt (f : A ⟶ X) :
    Continuous fun p : unitInterval × topologicalSuspension A ↦
      topologicalSecondBottomHeightRaiseAt f
        (TopCat.I.homeomorph.symm p.1) p.2 := by
  apply (topologicalMappingConeTripleDesc_isQuotientMap
    (toUnit A)).continuous_lift_prod_right
  let L :
      (unitInterval × (A ⊗ TopCat.I : TopCat.{u})) ⊕
        (unitInterval × (𝟙_ TopCat.{u})) →
          topologicalMappingCone (topologicalMappingConeCollapse f) :=
    Sum.elim
      (fun p ↦ topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeConeIncl f
              (topologicalConeCylinderIncl A p.2),
            TopCat.I.mul
              (snd A TopCat.I p.2, TopCat.I.homeomorph.symm p.1))))
      (fun p ↦ topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A p.2),
            TopCat.I.homeomorph.symm p.1)))
  have hL : Continuous L := by
    rw [continuous_sum_dom]
    constructor <;> dsimp [L] <;> fun_prop
  have hright : Continuous (fun p : unitInterval ×
      ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u})) ↦
      match p.2 with
      | Sum.inl c => topologicalMappingConeConeIncl
          (topologicalMappingConeCollapse f)
            (topologicalConeCylinderIncl (topologicalMappingCone f)
              (topologicalMappingConeConeIncl f
                  (topologicalConeCylinderIncl A c),
                TopCat.I.mul
                  (snd A TopCat.I c, TopCat.I.homeomorph.symm p.1)))
      | Sum.inr z => topologicalMappingConeConeIncl
          (topologicalMappingConeCollapse f)
            (topologicalConeCylinderIncl (topologicalMappingCone f)
              (topologicalMappingConeConeIncl f (topologicalConePointIncl A z),
                TopCat.I.homeomorph.symm p.1))) := by
    have hcomp := hL.comp (Homeomorph.prodSumDistrib :
      unitInterval × ((A ⊗ TopCat.I : TopCat.{u}) ⊕
        (𝟙_ TopCat.{u})) ≃ₜ _).continuous
    convert hcomp using 1
    funext p
    rcases p with ⟨t, c | z⟩ <;> rfl
  let K :
      (unitInterval × (𝟙_ TopCat.{u})) ⊕
        (unitInterval × ((A ⊗ TopCat.I : TopCat.{u}) ⊕
          (𝟙_ TopCat.{u}))) →
            topologicalMappingCone (topologicalMappingConeCollapse f) :=
    Sum.elim
      (fun p ↦ topologicalMappingConeIncl (topologicalMappingConeCollapse f)
        (topologicalSuspensionPointIncl A p.2))
      (fun p ↦ match p.2 with
        | Sum.inl c => topologicalMappingConeConeIncl
            (topologicalMappingConeCollapse f)
              (topologicalConeCylinderIncl (topologicalMappingCone f)
                (topologicalMappingConeConeIncl f
                    (topologicalConeCylinderIncl A c),
                  TopCat.I.mul
                    (snd A TopCat.I c, TopCat.I.homeomorph.symm p.1)))
        | Sum.inr z => topologicalMappingConeConeIncl
            (topologicalMappingConeCollapse f)
              (topologicalConeCylinderIncl (topologicalMappingCone f)
                (topologicalMappingConeConeIncl f (topologicalConePointIncl A z),
                  TopCat.I.homeomorph.symm p.1)))
  have hK : Continuous K := by
    rw [continuous_sum_dom]
    exact ⟨by dsimp [K]; fun_prop, by simpa [K] using hright⟩
  have hcomp := hK.comp (Homeomorph.prodSumDistrib :
    unitInterval × ((𝟙_ TopCat.{u} : Type u) ⊕
      ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u}))) ≃ₜ _).continuous
  convert hcomp using 1
  funext p
  rcases p with ⟨t, z | r⟩
  · change topologicalSecondBottomHeightRaiseAt f
        (TopCat.I.homeomorph.symm t) (topologicalSuspensionPointIncl A z) =
      K (Homeomorph.prodSumDistrib (t, Sum.inl z))
    rw [show (Homeomorph.prodSumDistrib (t, Sum.inl z) :
      (unitInterval × (𝟙_ TopCat.{u})) ⊕ _) = Sum.inl (t, z) from rfl]
    simp [K]
  · rcases r with c | z
    · change topologicalSecondBottomHeightRaiseAt f
          (TopCat.I.homeomorph.symm t)
            (topologicalSuspensionConeIncl A
              (topologicalConeCylinderIncl A c)) =
        K (Homeomorph.prodSumDistrib (t, Sum.inr (Sum.inl c)))
      rw [show (Homeomorph.prodSumDistrib (t, Sum.inr (Sum.inl c)) :
        (unitInterval × (𝟙_ TopCat.{u})) ⊕ _) =
          Sum.inr (t, Sum.inl c) from rfl]
      dsimp [K]
      rcases c with ⟨a, u⟩
      exact topologicalSecondBottomHeightRaiseAt_cylinder f
        (TopCat.I.homeomorph.symm t) a u
    · change topologicalSecondBottomHeightRaiseAt f
          (TopCat.I.homeomorph.symm t)
            (topologicalSuspensionConeIncl A (topologicalConePointIncl A z)) =
        K (Homeomorph.prodSumDistrib (t, Sum.inr (Sum.inr z)))
      rw [show (Homeomorph.prodSumDistrib (t, Sum.inr (Sum.inr z)) :
        (unitInterval × (𝟙_ TopCat.{u})) ⊕ _) =
          Sum.inr (t, Sum.inr z) from rfl]
      simp [K]

@[simp]
theorem topologicalSecondHeightRaiseAt_zero (f : A ⟶ X) :
    topologicalSecondHeightRaiseAt f 0 =
      𝟙 (topologicalMappingCone (topologicalMappingConeCollapse f)) := by
  apply topologicalMappingCone_hom_ext (topologicalMappingConeCollapse f)
  · rw [topologicalSecondMappingConeIncl_heightRaiseAt,
      topologicalSecondBottomHeightRaiseAt_zero, Category.comp_id]
  · rw [topologicalSecondMappingConeConeIncl_heightRaiseAt,
      topologicalSecondConeHeightRaiseAt_zero,
      Category.id_comp, Category.comp_id]

/-- The height normalization of the second mapping cone is jointly continuous in time and in
the iterated mapping-cone variable. -/
theorem continuous_topologicalSecondHeightRaiseAt (f : A ⟶ X) :
    Continuous fun p : unitInterval ×
        topologicalMappingCone (topologicalMappingConeCollapse f) ↦
      topologicalSecondHeightRaiseAt f
        (TopCat.I.homeomorph.symm p.1) p.2 := by
  apply (topologicalMappingConeTripleDesc_isQuotientMap
    (topologicalMappingConeCollapse f)).continuous_lift_prod_right
  let L :
      (unitInterval × (topologicalMappingCone f ⊗ TopCat.I : TopCat.{u})) ⊕
        (unitInterval × (𝟙_ TopCat.{u})) →
          topologicalMappingCone (topologicalMappingConeCollapse f) :=
    Sum.elim
      (fun p ↦ topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (fst (topologicalMappingCone f) TopCat.I p.2,
            TopCat.I.max (snd (topologicalMappingCone f) TopCat.I p.2,
              TopCat.I.mul
                (topologicalMappingConeHeight f
                    (fst (topologicalMappingCone f) TopCat.I p.2),
                  TopCat.I.homeomorph.symm p.1)))))
      (fun p ↦ topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConePointIncl (topologicalMappingCone f) p.2))
  have hL : Continuous L := by
    rw [continuous_sum_dom]
    constructor <;> dsimp [L] <;> fun_prop
  have hright : Continuous (fun p : unitInterval ×
      ((topologicalMappingCone f ⊗ TopCat.I : TopCat.{u}) ⊕
        (𝟙_ TopCat.{u})) ↦
      match p.2 with
      | Sum.inl c => topologicalMappingConeConeIncl
          (topologicalMappingConeCollapse f)
            (topologicalConeCylinderIncl (topologicalMappingCone f)
              (fst (topologicalMappingCone f) TopCat.I c,
                TopCat.I.max (snd (topologicalMappingCone f) TopCat.I c,
                  TopCat.I.mul
                    (topologicalMappingConeHeight f
                        (fst (topologicalMappingCone f) TopCat.I c),
                      TopCat.I.homeomorph.symm p.1))))
      | Sum.inr z => topologicalMappingConeConeIncl
          (topologicalMappingConeCollapse f)
            (topologicalConePointIncl (topologicalMappingCone f) z)) := by
    have hcomp := hL.comp (Homeomorph.prodSumDistrib :
      unitInterval ×
        ((topologicalMappingCone f ⊗ TopCat.I : TopCat.{u}) ⊕
          (𝟙_ TopCat.{u})) ≃ₜ _).continuous
    convert hcomp using 1
    funext p
    rcases p with ⟨t, c | z⟩ <;> rfl
  let K :
      (unitInterval × (topologicalSuspension A : Type u)) ⊕
        (unitInterval ×
          ((topologicalMappingCone f ⊗ TopCat.I : TopCat.{u}) ⊕
            (𝟙_ TopCat.{u}))) →
              topologicalMappingCone (topologicalMappingConeCollapse f) :=
    Sum.elim
      (fun p ↦ topologicalSecondBottomHeightRaiseAt f
        (TopCat.I.homeomorph.symm p.1) p.2)
      (fun p ↦ match p.2 with
        | Sum.inl c => topologicalMappingConeConeIncl
            (topologicalMappingConeCollapse f)
              (topologicalConeCylinderIncl (topologicalMappingCone f)
                (fst (topologicalMappingCone f) TopCat.I c,
                  TopCat.I.max (snd (topologicalMappingCone f) TopCat.I c,
                    TopCat.I.mul
                      (topologicalMappingConeHeight f
                          (fst (topologicalMappingCone f) TopCat.I c),
                        TopCat.I.homeomorph.symm p.1))))
        | Sum.inr z => topologicalMappingConeConeIncl
            (topologicalMappingConeCollapse f)
              (topologicalConePointIncl (topologicalMappingCone f) z))
  have hK : Continuous K := by
    rw [continuous_sum_dom]
    exact ⟨continuous_topologicalSecondBottomHeightRaiseAt f,
      by simpa [K] using hright⟩
  have hcomp := hK.comp (Homeomorph.prodSumDistrib :
    unitInterval × ((topologicalSuspension A : Type u) ⊕
      ((topologicalMappingCone f ⊗ TopCat.I : TopCat.{u}) ⊕
        (𝟙_ TopCat.{u}))) ≃ₜ _).continuous
  convert hcomp using 1
  funext p
  rcases p with ⟨t, y | r⟩
  · change topologicalSecondHeightRaiseAt f
        (TopCat.I.homeomorph.symm t)
          (topologicalMappingConeIncl (topologicalMappingConeCollapse f) y) =
      K (Homeomorph.prodSumDistrib (t, Sum.inl y))
    rw [show (Homeomorph.prodSumDistrib (t, Sum.inl y) :
      (unitInterval × (topologicalSuspension A : Type u)) ⊕ _) =
        Sum.inl (t, y) from rfl]
    dsimp [K]
    exact ConcreteCategory.congr_hom
      (topologicalSecondMappingConeIncl_heightRaiseAt f
        (TopCat.I.homeomorph.symm t)) y
  · rcases r with c | z
    · change topologicalSecondHeightRaiseAt f
          (TopCat.I.homeomorph.symm t)
            (topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
              (topologicalConeCylinderIncl (topologicalMappingCone f) c)) =
        K (Homeomorph.prodSumDistrib (t, Sum.inr (Sum.inl c)))
      rw [show (Homeomorph.prodSumDistrib (t, Sum.inr (Sum.inl c)) :
        (unitInterval × (topologicalSuspension A : Type u)) ⊕ _) =
          Sum.inr (t, Sum.inl c) from rfl]
      dsimp [K]
      rw [show topologicalSecondHeightRaiseAt f
          (TopCat.I.homeomorph.symm t)
            (topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
              (topologicalConeCylinderIncl (topologicalMappingCone f) c)) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalSecondConeHeightRaiseAt f
            (TopCat.I.homeomorph.symm t)
              (topologicalConeCylinderIncl (topologicalMappingCone f) c)) from
          ConcreteCategory.congr_hom
            (topologicalSecondMappingConeConeIncl_heightRaiseAt f
              (TopCat.I.homeomorph.symm t))
            (topologicalConeCylinderIncl (topologicalMappingCone f) c)]
      rcases c with ⟨c, v⟩
      exact congrArg
        (topologicalMappingConeConeIncl (topologicalMappingConeCollapse f))
        (topologicalSecondConeHeightRaiseAt_cylinder f
          (TopCat.I.homeomorph.symm t) c v)
    · change topologicalSecondHeightRaiseAt f
          (TopCat.I.homeomorph.symm t)
            (topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
              (topologicalConePointIncl (topologicalMappingCone f) z)) =
        K (Homeomorph.prodSumDistrib (t, Sum.inr (Sum.inr z)))
      rw [show (Homeomorph.prodSumDistrib (t, Sum.inr (Sum.inr z)) :
        (unitInterval × (topologicalSuspension A : Type u)) ⊕ _) =
          Sum.inr (t, Sum.inr z) from rfl]
      dsimp [K]
      rw [show topologicalSecondHeightRaiseAt f
          (TopCat.I.homeomorph.symm t)
            (topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
              (topologicalConePointIncl (topologicalMappingCone f) z)) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalSecondConeHeightRaiseAt f
            (TopCat.I.homeomorph.symm t)
              (topologicalConePointIncl (topologicalMappingCone f) z)) from
          ConcreteCategory.congr_hom
            (topologicalSecondMappingConeConeIncl_heightRaiseAt f
              (TopCat.I.homeomorph.symm t))
            (topologicalConePointIncl (topologicalMappingCone f) z)]
      exact congrArg
        (topologicalMappingConeConeIncl (topologicalMappingConeCollapse f))
        (ConcreteCategory.congr_hom
          (topologicalSecondConePointIncl_heightRaiseAt f
            (TopCat.I.homeomorph.symm t)) z)

/-- The quotient-compatible height normalization is a homotopy from the identity on the second
mapping cone to its time-one normalization. -/
def topologicalSecondHeightRaiseHomotopy (f : A ⟶ X) :
    TopCat.Homotopy
      (𝟙 (topologicalMappingCone (topologicalMappingConeCollapse f)))
      (topologicalSecondHeightRaiseAt f 1) where
  toFun p := topologicalSecondHeightRaiseAt f
    (TopCat.I.homeomorph.symm p.1) p.2
  continuous_toFun := continuous_topologicalSecondHeightRaiseAt f
  map_zero_left z := by
    change topologicalSecondHeightRaiseAt f 0 z = z
    rw [topologicalSecondHeightRaiseAt_zero]
    rfl
  map_one_left z := by
    change topologicalSecondHeightRaiseAt f 1 z = _
    rfl

/-- At time one, the outer cylinder height becomes the maximum of its original height and the
inner mapping-cone height. -/
theorem topologicalSecondConeHeightRaiseAt_one_cylinder
    (f : A ⟶ X) (c : topologicalMappingCone f) (v : TopCat.I) :
    topologicalSecondConeHeightRaiseAt f 1
        (topologicalConeCylinderIncl (topologicalMappingCone f) (c, v)) =
      topologicalConeCylinderIncl (topologicalMappingCone f)
        (c, TopCat.I.max (v, topologicalMappingConeHeight f c)) := by
  rw [show topologicalSecondConeHeightRaiseAt f 1
      (topologicalConeCylinderIncl (topologicalMappingCone f) (c, v)) =
    topologicalConeCylinderIncl (topologicalMappingCone f)
      (topologicalSecondConeHeightRaiseCylinderAt f 1 (c, v)) from
        ConcreteCategory.congr_hom
          (topologicalSecondConeCylinderIncl_heightRaiseAt f 1) (c, v)]
  simp

/-- The normalization fixes the outer cone on the original-space summand of `C_f`. -/
theorem topologicalSecondConeHeightRaiseAt_one_incl
    (f : A ⟶ X) (x : X) (v : TopCat.I) :
    topologicalSecondConeHeightRaiseAt f 1
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeIncl f x, v)) =
      topologicalConeCylinderIncl (topologicalMappingCone f)
        (topologicalMappingConeIncl f x, v) := by
  rw [topologicalSecondConeHeightRaiseAt_one_cylinder]
  have hheight := ConcreteCategory.congr_hom
    (topologicalMappingConeIncl_height f) x
  change topologicalMappingConeHeight f (topologicalMappingConeIncl f x) = 0 at hheight
  rw [hheight, TopCat.I.max_zero_right]

/-- On the iterated cone-cylinder piece, time one replaces the outer height by the maximum of
the two cone heights. -/
theorem topologicalSecondConeHeightRaiseAt_one_doubleCylinder
    (f : A ⟶ X) (a : A) (u v : TopCat.I) :
    topologicalSecondConeHeightRaiseAt f 1
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A (a, u)), v)) =
      topologicalConeCylinderIncl (topologicalMappingCone f)
        (topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A (a, u)), TopCat.I.max (v, u)) := by
  rw [topologicalSecondConeHeightRaiseAt_one_cylinder]
  have hheight := ConcreteCategory.congr_hom
    (topologicalMappingConeConeIncl_height f) (topologicalConeCylinderIncl A (a, u))
  change topologicalMappingConeHeight f
      (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A (a, u))) =
    topologicalConeHeight A (topologicalConeCylinderIncl A (a, u)) at hheight
  rw [hheight]
  have hcone := ConcreteCategory.congr_hom
    (topologicalConeCylinderIncl_height A) (a, u)
  change topologicalConeHeight A (topologicalConeCylinderIncl A (a, u)) = u at hcone
  rw [hcone]

/-- At time one, the outer cylinder over the inner cone apex has reached the outer cone apex. -/
theorem topologicalSecondConeHeightRaiseAt_one_innerApex
    (f : A ⟶ X) (z : 𝟙_ TopCat.{u}) (v : TopCat.I) :
    topologicalSecondConeHeightRaiseAt f 1
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z), v)) =
      topologicalConePointIncl (topologicalMappingCone f) PUnit.unit := by
  rw [topologicalSecondConeHeightRaiseAt_one_cylinder]
  have hheight := ConcreteCategory.congr_hom
    (topologicalMappingConeConeIncl_height f) (topologicalConePointIncl A z)
  change topologicalMappingConeHeight f
      (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
    topologicalConeHeight A (topologicalConePointIncl A z) at hheight
  rw [hheight]
  have hcone := ConcreteCategory.congr_hom
    (topologicalConePointIncl_height A) z
  change topologicalConeHeight A (topologicalConePointIncl A z) = 1 at hcone
  rw [hcone, TopCat.I.max_one_right]
  exact ConcreteCategory.congr_hom (pushout.condition :
    (TopCat.ι₁ : topologicalMappingCone f ⟶
        topologicalMappingCone f ⊗ TopCat.I) ≫
          topologicalConeCylinderIncl (topologicalMappingCone f) =
      toUnit (topologicalMappingCone f) ≫
        topologicalConePointIncl (topologicalMappingCone f))
    (topologicalMappingConeConeIncl f (topologicalConePointIncl A z))

/-- The outer-cone height normalization as a continuous homotopy from the identity to its
time-one map. -/
def topologicalSecondConeHeightRaiseHomotopy (f : A ⟶ X) :
    TopCat.Homotopy (𝟙 (topologicalCone (topologicalMappingCone f)))
      (topologicalSecondConeHeightRaiseAt f 1) where
  toFun p := topologicalSecondConeHeightRaiseAt f
    (TopCat.I.homeomorph.symm p.1) p.2
  continuous_toFun := by
    apply (topologicalConeSumDesc_isQuotientMap
      (topologicalMappingCone f)).continuous_lift_prod_right
    let K :
        (unitInterval ×
            (topologicalMappingCone f ⊗ TopCat.I : TopCat.{u})) ⊕
          (unitInterval × (𝟙_ TopCat.{u})) →
            topologicalCone (topologicalMappingCone f) :=
      Sum.elim
        (fun p ↦ topologicalConeCylinderIncl (topologicalMappingCone f)
          (fst (topologicalMappingCone f) TopCat.I p.2,
            TopCat.I.max (snd (topologicalMappingCone f) TopCat.I p.2,
            TopCat.I.mul (topologicalMappingConeHeight f
                (fst (topologicalMappingCone f) TopCat.I p.2),
              TopCat.I.homeomorph.symm p.1))))
        (fun p ↦ topologicalConePointIncl (topologicalMappingCone f) p.2)
    have hK : Continuous K := by
      rw [continuous_sum_dom]
      constructor <;> dsimp [K] <;> fun_prop
    have hcomp := hK.comp (Homeomorph.prodSumDistrib :
      unitInterval ×
          ((topologicalMappingCone f ⊗ TopCat.I : TopCat.{u}) ⊕
            (𝟙_ TopCat.{u})) ≃ₜ _).continuous
    convert hcomp using 1
    funext p
    rcases p with ⟨t, c | z⟩
    · change topologicalSecondConeHeightRaiseAt f
        (TopCat.I.homeomorph.symm t)
          (topologicalConeCylinderIncl (topologicalMappingCone f) c) = _
      exact ConcreteCategory.congr_hom
        (topologicalSecondConeCylinderIncl_heightRaiseAt f
          (TopCat.I.homeomorph.symm t)) c
    · change topologicalSecondConeHeightRaiseAt f
        (TopCat.I.homeomorph.symm t)
          (topologicalConePointIncl (topologicalMappingCone f) z) = _
      exact ConcreteCategory.congr_hom
        (topologicalSecondConePointIncl_heightRaiseAt f
          (TopCat.I.homeomorph.symm t)) z
  map_zero_left z := by
    change topologicalSecondConeHeightRaiseAt f 0 z = z
    rw [topologicalSecondConeHeightRaiseAt_zero]
    rfl
  map_one_left z := by
    change topologicalSecondConeHeightRaiseAt f 1 z = _
    rfl

end Submission
