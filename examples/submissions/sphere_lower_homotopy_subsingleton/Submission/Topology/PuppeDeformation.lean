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
theorem topologicalSecondConeHeightRaiseAt_zero (f : A ⟶ X) :
    topologicalSecondConeHeightRaiseAt f 0 =
      𝟙 (topologicalCone (topologicalMappingCone f)) := by
  apply topologicalCone_hom_ext (topologicalMappingCone f)
  · rw [topologicalSecondConeCylinderIncl_heightRaiseAt,
      topologicalSecondConeHeightRaiseCylinderAt_zero,
      Category.id_comp, Category.comp_id]
  · rw [topologicalSecondConePointIncl_heightRaiseAt, Category.comp_id]

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
