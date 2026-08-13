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

/-- At fixed deformation time, the descended first-mapping-cone formula varies jointly
continuously with the outer height and the point of `C_f`. -/
theorem continuous_topologicalSecondMappingConeHeightShrinkAt
    (f : A ⟶ X) (t : TopCat.I) :
    Continuous fun p : (TopCat.I.{u} : Type u) × topologicalMappingCone f ↦
      topologicalSecondMappingConeHeightShrinkAt f t p.1 p.2 := by
  apply (topologicalMappingConeTripleDesc_isQuotientMap f).continuous_lift_prod_right
  let L :
      ((TopCat.I.{u} : Type u) × (A ⊗ TopCat.I : TopCat.{u})) ⊕
        ((TopCat.I.{u} : Type u) × (𝟙_ TopCat.{u})) →
          topologicalMappingCone (topologicalMappingConeCollapse f) :=
    Sum.elim
      (fun p ↦ topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeConeIncl f
              (topologicalConeCylinderIncl A
                (fst A TopCat.I p.2,
                  TopCat.I.mul
                    (snd A TopCat.I p.2, TopCat.I.symm t))),
            TopCat.I.max (p.1, snd A TopCat.I p.2))))
      (fun _ ↦ topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConePointIncl (topologicalMappingCone f) PUnit.unit))
  have hL : Continuous L := by
    rw [continuous_sum_dom]
    constructor <;> dsimp [L] <;> fun_prop
  have hright : Continuous (fun p : (TopCat.I.{u} : Type u) ×
      ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u})) ↦
      match p.2 with
      | Sum.inl c => topologicalMappingConeConeIncl
          (topologicalMappingConeCollapse f)
            (topologicalConeCylinderIncl (topologicalMappingCone f)
              (topologicalMappingConeConeIncl f
                  (topologicalConeCylinderIncl A
                    (fst A TopCat.I c,
                      TopCat.I.mul (snd A TopCat.I c, TopCat.I.symm t))),
                TopCat.I.max (p.1, snd A TopCat.I c)))
      | Sum.inr _ => topologicalMappingConeConeIncl
          (topologicalMappingConeCollapse f)
            (topologicalConePointIncl (topologicalMappingCone f) PUnit.unit)) := by
    have hcomp := hL.comp (Homeomorph.prodSumDistrib :
      (TopCat.I.{u} : Type u) ×
        ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u})) ≃ₜ _).continuous
    convert hcomp using 1
    funext p
    rcases p with ⟨v, c | z⟩ <;> rfl
  let K :
      ((TopCat.I.{u} : Type u) × (X : Type u)) ⊕
        ((TopCat.I.{u} : Type u) ×
          ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u}))) →
            topologicalMappingCone (topologicalMappingConeCollapse f) :=
    Sum.elim
      (fun p ↦ topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeIncl f p.2, p.1)))
      (fun p ↦ match p.2 with
        | Sum.inl c => topologicalMappingConeConeIncl
            (topologicalMappingConeCollapse f)
              (topologicalConeCylinderIncl (topologicalMappingCone f)
                (topologicalMappingConeConeIncl f
                    (topologicalConeCylinderIncl A
                      (fst A TopCat.I c,
                        TopCat.I.mul (snd A TopCat.I c, TopCat.I.symm t))),
                  TopCat.I.max (p.1, snd A TopCat.I c)))
        | Sum.inr _ => topologicalMappingConeConeIncl
            (topologicalMappingConeCollapse f)
              (topologicalConePointIncl (topologicalMappingCone f) PUnit.unit))
  have hK : Continuous K := by
    rw [continuous_sum_dom]
    exact ⟨by dsimp [K]; fun_prop, by simpa [K] using hright⟩
  have hcomp := hK.comp (Homeomorph.prodSumDistrib :
    (TopCat.I.{u} : Type u) × ((X : Type u) ⊕
      ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u}))) ≃ₜ _).continuous
  convert hcomp using 1
  funext p
  rcases p with ⟨v, x | r⟩
  · change topologicalSecondMappingConeHeightShrinkAt f t v
        (topologicalMappingConeIncl f x) =
      K (Homeomorph.prodSumDistrib (v, Sum.inl x))
    rw [show (Homeomorph.prodSumDistrib (v, Sum.inl x) :
      ((TopCat.I.{u} : Type u) × (X : Type u)) ⊕ _) = Sum.inl (v, x) from rfl]
    dsimp [K]
    exact ConcreteCategory.congr_hom
      (topologicalMappingConeIncl_secondHeightShrinkAt f t v) x
  · rcases r with c | z
    · change topologicalSecondMappingConeHeightShrinkAt f t v
          (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c)) =
        K (Homeomorph.prodSumDistrib (v, Sum.inr (Sum.inl c)))
      rw [show (Homeomorph.prodSumDistrib (v, Sum.inr (Sum.inl c)) :
        ((TopCat.I.{u} : Type u) × (X : Type u)) ⊕ _) =
          Sum.inr (v, Sum.inl c) from rfl]
      dsimp [K]
      rw [show topologicalSecondMappingConeHeightShrinkAt f t v
          (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c)) =
        topologicalSecondInnerHeightShrinkConeAt f t v
          (topologicalConeCylinderIncl A c) from
          ConcreteCategory.congr_hom
            (topologicalMappingConeConeIncl_secondHeightShrinkAt f t v)
            (topologicalConeCylinderIncl A c)]
      rcases c with ⟨a, u⟩
      rw [show topologicalSecondInnerHeightShrinkConeAt f t v
          (topologicalConeCylinderIncl A (a, u)) =
        topologicalSecondInnerHeightShrinkCylinderAt f t v (a, u) from
          ConcreteCategory.congr_hom
            (topologicalConeCylinderIncl_secondInnerHeightShrinkConeAt f t v)
            (a, u)]
      exact topologicalSecondInnerHeightShrinkCylinderAt_apply f t v a u
    · change topologicalSecondMappingConeHeightShrinkAt f t v
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
        K (Homeomorph.prodSumDistrib (v, Sum.inr (Sum.inr z)))
      rw [show (Homeomorph.prodSumDistrib (v, Sum.inr (Sum.inr z)) :
        ((TopCat.I.{u} : Type u) × (X : Type u)) ⊕ _) =
          Sum.inr (v, Sum.inr z) from rfl]
      dsimp [K]
      rw [show topologicalSecondMappingConeHeightShrinkAt f t v
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
        topologicalSecondInnerHeightShrinkConeAt f t v
          (topologicalConePointIncl A z) from
          ConcreteCategory.congr_hom
            (topologicalMappingConeConeIncl_secondHeightShrinkAt f t v)
            (topologicalConePointIncl A z)]
      exact ConcreteCategory.congr_hom
        (topologicalConePointIncl_secondInnerHeightShrinkConeAt f t v) z

/-- The descended first-mapping-cone formula is jointly continuous in deformation time, outer
height, and the point of `C_f`. -/
theorem continuous_topologicalSecondMappingConeHeightShrinkAt_joint
    (f : A ⟶ X) :
    Continuous fun p :
        ((TopCat.I.{u} : Type u) × (TopCat.I.{u} : Type u)) ×
          topologicalMappingCone f ↦
      topologicalSecondMappingConeHeightShrinkAt f p.1.1 p.1.2 p.2 := by
  apply (topologicalMappingConeTripleDesc_isQuotientMap f).continuous_lift_prod_right
  let L :
      (((TopCat.I.{u} : Type u) × (TopCat.I.{u} : Type u)) ×
          (A ⊗ TopCat.I : TopCat.{u})) ⊕
        (((TopCat.I.{u} : Type u) × (TopCat.I.{u} : Type u)) ×
          (𝟙_ TopCat.{u})) →
            topologicalMappingCone (topologicalMappingConeCollapse f) :=
    Sum.elim
      (fun p ↦ topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeConeIncl f
              (topologicalConeCylinderIncl A
                (fst A TopCat.I p.2,
                  TopCat.I.mul
                    (snd A TopCat.I p.2, TopCat.I.symm p.1.1))),
            TopCat.I.max (p.1.2, snd A TopCat.I p.2))))
      (fun _ ↦ topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConePointIncl (topologicalMappingCone f) PUnit.unit))
  have hL : Continuous L := by
    rw [continuous_sum_dom]
    constructor <;> dsimp [L] <;> fun_prop
  have hright : Continuous (fun p :
      ((TopCat.I.{u} : Type u) × (TopCat.I.{u} : Type u)) ×
        ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u})) ↦
      match p.2 with
      | Sum.inl c => topologicalMappingConeConeIncl
          (topologicalMappingConeCollapse f)
            (topologicalConeCylinderIncl (topologicalMappingCone f)
              (topologicalMappingConeConeIncl f
                  (topologicalConeCylinderIncl A
                    (fst A TopCat.I c,
                      TopCat.I.mul
                        (snd A TopCat.I c, TopCat.I.symm p.1.1))),
                TopCat.I.max (p.1.2, snd A TopCat.I c)))
      | Sum.inr _ => topologicalMappingConeConeIncl
          (topologicalMappingConeCollapse f)
            (topologicalConePointIncl (topologicalMappingCone f) PUnit.unit)) := by
    have hcomp := hL.comp (Homeomorph.prodSumDistrib :
      ((TopCat.I.{u} : Type u) × (TopCat.I.{u} : Type u)) ×
        ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u})) ≃ₜ _).continuous
    convert hcomp using 1
    funext p
    rcases p with ⟨tv, c | z⟩ <;> rfl
  let K :
      (((TopCat.I.{u} : Type u) × (TopCat.I.{u} : Type u)) ×
          (X : Type u)) ⊕
        (((TopCat.I.{u} : Type u) × (TopCat.I.{u} : Type u)) ×
          ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u}))) →
            topologicalMappingCone (topologicalMappingConeCollapse f) :=
    Sum.elim
      (fun p ↦ topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeIncl f p.2, p.1.2)))
      (fun p ↦ match p.2 with
        | Sum.inl c => topologicalMappingConeConeIncl
            (topologicalMappingConeCollapse f)
              (topologicalConeCylinderIncl (topologicalMappingCone f)
                (topologicalMappingConeConeIncl f
                    (topologicalConeCylinderIncl A
                      (fst A TopCat.I c,
                        TopCat.I.mul
                          (snd A TopCat.I c, TopCat.I.symm p.1.1))),
                  TopCat.I.max (p.1.2, snd A TopCat.I c)))
        | Sum.inr _ => topologicalMappingConeConeIncl
            (topologicalMappingConeCollapse f)
              (topologicalConePointIncl (topologicalMappingCone f) PUnit.unit))
  have hK : Continuous K := by
    rw [continuous_sum_dom]
    exact ⟨by dsimp [K]; fun_prop, by simpa [K] using hright⟩
  have hcomp := hK.comp (Homeomorph.prodSumDistrib :
    ((TopCat.I.{u} : Type u) × (TopCat.I.{u} : Type u)) ×
      ((X : Type u) ⊕ ((A ⊗ TopCat.I : TopCat.{u}) ⊕
        (𝟙_ TopCat.{u}))) ≃ₜ _).continuous
  convert hcomp using 1
  funext p
  rcases p with ⟨⟨t, v⟩, x | r⟩
  · change topologicalSecondMappingConeHeightShrinkAt f t v
        (topologicalMappingConeIncl f x) =
      K (Homeomorph.prodSumDistrib ((t, v), Sum.inl x))
    rw [show (Homeomorph.prodSumDistrib ((t, v), Sum.inl x) :
      ((((TopCat.I.{u} : Type u) × (TopCat.I.{u} : Type u)) ×
          (X : Type u)) ⊕ _)) = Sum.inl ((t, v), x) from rfl]
    dsimp [K]
    exact ConcreteCategory.congr_hom
      (topologicalMappingConeIncl_secondHeightShrinkAt f t v) x
  · rcases r with c | z
    · change topologicalSecondMappingConeHeightShrinkAt f t v
          (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c)) =
        K (Homeomorph.prodSumDistrib ((t, v), Sum.inr (Sum.inl c)))
      rw [show (Homeomorph.prodSumDistrib ((t, v), Sum.inr (Sum.inl c)) :
        ((((TopCat.I.{u} : Type u) × (TopCat.I.{u} : Type u)) ×
            (X : Type u)) ⊕ _)) =
          Sum.inr ((t, v), Sum.inl c) from rfl]
      dsimp [K]
      rw [show topologicalSecondMappingConeHeightShrinkAt f t v
          (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c)) =
        topologicalSecondInnerHeightShrinkConeAt f t v
          (topologicalConeCylinderIncl A c) from
          ConcreteCategory.congr_hom
            (topologicalMappingConeConeIncl_secondHeightShrinkAt f t v)
            (topologicalConeCylinderIncl A c)]
      rcases c with ⟨a, u⟩
      rw [show topologicalSecondInnerHeightShrinkConeAt f t v
          (topologicalConeCylinderIncl A (a, u)) =
        topologicalSecondInnerHeightShrinkCylinderAt f t v (a, u) from
          ConcreteCategory.congr_hom
            (topologicalConeCylinderIncl_secondInnerHeightShrinkConeAt f t v)
            (a, u)]
      exact topologicalSecondInnerHeightShrinkCylinderAt_apply f t v a u
    · change topologicalSecondMappingConeHeightShrinkAt f t v
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
        K (Homeomorph.prodSumDistrib ((t, v), Sum.inr (Sum.inr z)))
      rw [show (Homeomorph.prodSumDistrib ((t, v), Sum.inr (Sum.inr z)) :
        ((((TopCat.I.{u} : Type u) × (TopCat.I.{u} : Type u)) ×
            (X : Type u)) ⊕ _)) =
          Sum.inr ((t, v), Sum.inr z) from rfl]
      dsimp [K]
      rw [show topologicalSecondMappingConeHeightShrinkAt f t v
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
        topologicalSecondInnerHeightShrinkConeAt f t v
          (topologicalConePointIncl A z) from
          ConcreteCategory.congr_hom
            (topologicalMappingConeConeIncl_secondHeightShrinkAt f t v)
            (topologicalConePointIncl A z)]
      exact ConcreteCategory.congr_hom
        (topologicalConePointIncl_secondInnerHeightShrinkConeAt f t v) z

/-- Swapping the two product variables gives the continuity statement in outer-cylinder order. -/
theorem continuous_topologicalSecondMappingConeHeightShrinkAt_swap
    (f : A ⟶ X) (t : TopCat.I) :
    Continuous fun p :
        (topologicalMappingCone f ⊗ TopCat.I : TopCat.{u}) ↦
      topologicalSecondMappingConeHeightShrinkAt f t p.2 p.1 := by
  have hswap : Continuous fun p :
      (topologicalMappingCone f ⊗ TopCat.I : TopCat.{u}) ↦ (p.2, p.1) := by
    fun_prop
  have hcomp :=
    (continuous_topologicalSecondMappingConeHeightShrinkAt f t).comp hswap
  convert hcomp using 1
  funext p
  rfl

/-- The fixed-time flattening on the cylinder of the outer cone. -/
def topologicalSecondHeightShrinkOuterCylinderAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalMappingCone f ⊗ TopCat.I ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  TopCat.ofHom
    { toFun := fun p ↦ topologicalSecondMappingConeHeightShrinkAt f t p.2 p.1
      continuous_toFun :=
        continuous_topologicalSecondMappingConeHeightShrinkAt_swap f t }

@[simp]
theorem topologicalSecondHeightShrinkOuterCylinderAt_apply
    (f : A ⟶ X) (t : TopCat.I) (c : topologicalMappingCone f) (v : TopCat.I) :
    topologicalSecondHeightShrinkOuterCylinderAt f t (c, v) =
      topologicalSecondMappingConeHeightShrinkAt f t v c :=
  rfl

@[reassoc]
theorem topologicalSecondOriginalHeightShrinkAt_one
    (f : A ⟶ X) :
    topologicalSecondOriginalHeightShrinkAt f 1 =
      toUnit X ≫ topologicalSecondInnerHeightShrinkPoint f := by
  apply TopCat.hom_ext
  ext x
  change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
      (topologicalConeCylinderIncl (topologicalMappingCone f)
        (topologicalMappingConeIncl f x, 1)) =
    topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
      (topologicalConePointIncl (topologicalMappingCone f) (toUnit X x))
  exact congrArg
    (topologicalMappingConeConeIncl (topologicalMappingConeCollapse f))
    (ConcreteCategory.congr_hom (pushout.condition :
      (TopCat.ι₁ : topologicalMappingCone f ⟶
          topologicalMappingCone f ⊗ TopCat.I) ≫
            topologicalConeCylinderIncl (topologicalMappingCone f) =
        toUnit (topologicalMappingCone f) ≫
          topologicalConePointIncl (topologicalMappingCone f))
      (topologicalMappingConeIncl f x))

@[reassoc]
theorem topologicalSecondInnerHeightShrinkConeAt_one
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalSecondInnerHeightShrinkConeAt f t 1 =
      toUnit (topologicalCone A) ≫ topologicalSecondInnerHeightShrinkPoint f := by
  apply topologicalCone_hom_ext A
  · apply TopCat.hom_ext
    ext p
    rcases p with ⟨a, u⟩
    change topologicalSecondInnerHeightShrinkConeAt f t 1
        (topologicalConeCylinderIncl A (a, u)) =
      topologicalSecondInnerHeightShrinkPoint f
        (toUnit (topologicalCone A) (topologicalConeCylinderIncl A (a, u)))
    rw [show topologicalSecondInnerHeightShrinkConeAt f t 1
        (topologicalConeCylinderIncl A (a, u)) =
      topologicalSecondInnerHeightShrinkCylinderAt f t 1 (a, u) from
        ConcreteCategory.congr_hom
          (topologicalConeCylinderIncl_secondInnerHeightShrinkConeAt f t 1)
          (a, u)]
    change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeConeIncl f
              (topologicalConeCylinderIncl A
                (a, TopCat.I.mul (u, TopCat.I.symm t))),
            TopCat.I.max (1, u))) =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConePointIncl (topologicalMappingCone f) PUnit.unit)
    rw [TopCat.I.max_one_left]
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
            (a, TopCat.I.mul (u, TopCat.I.symm t)))))
  · rw [topologicalConePointIncl_secondInnerHeightShrinkConeAt]
    apply TopCat.hom_ext
    ext z
    rfl

@[reassoc]
theorem topologicalSecondMappingConeHeightShrinkAt_one
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalSecondMappingConeHeightShrinkAt f t 1 =
      toUnit (topologicalMappingCone f) ≫
        topologicalSecondInnerHeightShrinkPoint f := by
  apply topologicalMappingCone_hom_ext f
  · rw [topologicalMappingConeIncl_secondHeightShrinkAt,
      topologicalSecondOriginalHeightShrinkAt_one]
    apply TopCat.hom_ext
    ext x
    rfl
  · rw [topologicalMappingConeConeIncl_secondHeightShrinkAt,
      topologicalSecondInnerHeightShrinkConeAt_one]
    apply TopCat.hom_ext
    ext c
    rfl

@[reassoc]
theorem topologicalSecondHeightShrinkOuter_ι₁
    (f : A ⟶ X) (t : TopCat.I) :
    TopCat.ι₁ ≫ topologicalSecondHeightShrinkOuterCylinderAt f t =
      toUnit (topologicalMappingCone f) ≫
        topologicalSecondInnerHeightShrinkPoint f := by
  apply TopCat.hom_ext
  ext c
  change topologicalSecondMappingConeHeightShrinkAt f t 1 c =
    topologicalSecondInnerHeightShrinkPoint f (toUnit (topologicalMappingCone f) c)
  exact ConcreteCategory.congr_hom
    (topologicalSecondMappingConeHeightShrinkAt_one f t) c

/-- The fixed-time flattening descends through the outer cone quotient. -/
def topologicalSecondHeightShrinkOuterConeAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalCone (topologicalMappingCone f) ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  topologicalConeDesc (topologicalMappingCone f)
    (topologicalSecondHeightShrinkOuterCylinderAt f t)
    (topologicalSecondInnerHeightShrinkPoint f)
    (topologicalSecondHeightShrinkOuter_ι₁ f t)

@[reassoc (attr := simp)]
theorem topologicalSecondConeCylinderIncl_heightShrinkOuterConeAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalConeCylinderIncl (topologicalMappingCone f) ≫
        topologicalSecondHeightShrinkOuterConeAt f t =
      topologicalSecondHeightShrinkOuterCylinderAt f t :=
  topologicalConeCylinderIncl_desc _ _ _ _

@[reassoc (attr := simp)]
theorem topologicalSecondConePointIncl_heightShrinkOuterConeAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalConePointIncl (topologicalMappingCone f) ≫
        topologicalSecondHeightShrinkOuterConeAt f t =
      topologicalSecondInnerHeightShrinkPoint f :=
  topologicalConePointIncl_desc _ _ _ _

@[reassoc]
theorem topologicalSecondOriginalHeightShrinkAt_zero
    (f : A ⟶ X) :
    topologicalSecondOriginalHeightShrinkAt f 0 =
      toUnit X ≫ topologicalSuspensionPointIncl A ≫
        topologicalMappingConeIncl (topologicalMappingConeCollapse f) := by
  apply TopCat.hom_ext
  ext x
  change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
      (topologicalConeCylinderIncl (topologicalMappingCone f)
        (topologicalMappingConeIncl f x, 0)) =
    topologicalMappingConeIncl (topologicalMappingConeCollapse f)
      (topologicalSuspensionPointIncl A (toUnit X x))
  have houter := ConcreteCategory.congr_hom
    (topologicalMappingCone_condition (topologicalMappingConeCollapse f))
    (topologicalMappingConeIncl f x)
  change topologicalMappingConeIncl (topologicalMappingConeCollapse f)
      (topologicalMappingConeCollapse f (topologicalMappingConeIncl f x)) =
    topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
      (topologicalConeCylinderIncl (topologicalMappingCone f)
        (topologicalMappingConeIncl f x, 0)) at houter
  rw [← houter]
  have hcollapse := ConcreteCategory.congr_hom
    (topologicalMappingConeIncl_collapse f) x
  change topologicalMappingConeCollapse f (topologicalMappingConeIncl f x) =
    topologicalSuspensionPointIncl A (toUnit X x) at hcollapse
  rw [hcollapse]

@[reassoc]
theorem topologicalSecondInnerHeightShrinkConeAt_base_zero
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalConeBaseIncl A ≫
        topologicalSecondInnerHeightShrinkConeAt f t 0 =
      toUnit A ≫ topologicalSuspensionPointIncl A ≫
        topologicalMappingConeIncl (topologicalMappingConeCollapse f) := by
  rw [← topologicalSecondInnerHeightShrink_base f t 0,
    topologicalSecondOriginalHeightShrinkAt_zero]
  apply TopCat.hom_ext
  ext a
  rfl

/-- The bottom suspension part of the fixed-time flattening. -/
def topologicalSecondHeightShrinkBottomAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalSuspension A ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  pushout.desc
    (topologicalSuspensionPointIncl A ≫
      topologicalMappingConeIncl (topologicalMappingConeCollapse f))
    (topologicalSecondInnerHeightShrinkConeAt f t 0)
    (topologicalSecondInnerHeightShrinkConeAt_base_zero f t).symm

@[reassoc (attr := simp)]
theorem topologicalSuspensionPointIncl_heightShrinkBottomAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalSuspensionPointIncl A ≫
        topologicalSecondHeightShrinkBottomAt f t =
      topologicalSuspensionPointIncl A ≫
        topologicalMappingConeIncl (topologicalMappingConeCollapse f) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalSuspensionConeIncl_heightShrinkBottomAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalSuspensionConeIncl A ≫
        topologicalSecondHeightShrinkBottomAt f t =
      topologicalSecondInnerHeightShrinkConeAt f t 0 :=
  pushout.inr_desc _ _ _

@[simp]
theorem topologicalSecondHeightShrinkOuterConeAt_base
    (f : A ⟶ X) (t : TopCat.I) (c : topologicalMappingCone f) :
    topologicalSecondHeightShrinkOuterConeAt f t
        (topologicalConeBaseIncl (topologicalMappingCone f) c) =
      topologicalSecondMappingConeHeightShrinkAt f t 0 c := by
  rw [show topologicalConeBaseIncl (topologicalMappingCone f) c =
    topologicalConeCylinderIncl (topologicalMappingCone f) (c, 0) from rfl]
  rw [show topologicalSecondHeightShrinkOuterConeAt f t
      (topologicalConeCylinderIncl (topologicalMappingCone f) (c, 0)) =
    topologicalSecondHeightShrinkOuterCylinderAt f t (c, 0) from
      ConcreteCategory.congr_hom
        (topologicalSecondConeCylinderIncl_heightShrinkOuterConeAt f t) (c, 0)]
  rfl

@[simp]
theorem topologicalSecondHeightShrinkBottomAt_point
    (f : A ⟶ X) (t : TopCat.I) (z : 𝟙_ TopCat.{u}) :
    topologicalSecondHeightShrinkBottomAt f t
        (topologicalSuspensionPointIncl A z) =
      topologicalMappingConeIncl (topologicalMappingConeCollapse f)
        (topologicalSuspensionPointIncl A z) := by
  exact ConcreteCategory.congr_hom
    (topologicalSuspensionPointIncl_heightShrinkBottomAt f t) z

@[simp]
theorem topologicalSecondHeightShrinkBottomAt_cone
    (f : A ⟶ X) (t : TopCat.I) (d : topologicalCone A) :
    topologicalSecondHeightShrinkBottomAt f t
        (topologicalSuspensionConeIncl A d) =
      topologicalSecondInnerHeightShrinkConeAt f t 0 d := by
  exact ConcreteCategory.congr_hom
    (topologicalSuspensionConeIncl_heightShrinkBottomAt f t) d

/-- The bottom and outer pieces of the fixed-time flattening agree on their common copy of
`C_f`. -/
@[reassoc]
theorem topologicalSecondHeightShrink_condition
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalMappingConeCollapse f ≫
        topologicalSecondHeightShrinkBottomAt f t =
      topologicalConeBaseIncl (topologicalMappingCone f) ≫
        topologicalSecondHeightShrinkOuterConeAt f t := by
  apply topologicalMappingCone_hom_ext f
  · apply TopCat.hom_ext
    ext x
    change topologicalSecondHeightShrinkBottomAt f t
        (topologicalMappingConeCollapse f (topologicalMappingConeIncl f x)) =
      topologicalSecondHeightShrinkOuterConeAt f t
        (topologicalConeBaseIncl (topologicalMappingCone f)
          (topologicalMappingConeIncl f x))
    have hcollapse := ConcreteCategory.congr_hom
      (topologicalMappingConeIncl_collapse f) x
    change topologicalMappingConeCollapse f (topologicalMappingConeIncl f x) =
      topologicalSuspensionPointIncl A (toUnit X x) at hcollapse
    rw [hcollapse, topologicalSecondHeightShrinkBottomAt_point,
      topologicalSecondHeightShrinkOuterConeAt_base]
    have horiginal := ConcreteCategory.congr_hom
      (topologicalMappingConeIncl_secondHeightShrinkAt f t 0) x
    change topologicalSecondMappingConeHeightShrinkAt f t 0
        (topologicalMappingConeIncl f x) =
      topologicalSecondOriginalHeightShrinkAt f 0 x at horiginal
    rw [horiginal]
    exact (ConcreteCategory.congr_hom
      (topologicalSecondOriginalHeightShrinkAt_zero f) x).symm
  · apply TopCat.hom_ext
    ext d
    change topologicalSecondHeightShrinkBottomAt f t
        (topologicalMappingConeCollapse f (topologicalMappingConeConeIncl f d)) =
      topologicalSecondHeightShrinkOuterConeAt f t
        (topologicalConeBaseIncl (topologicalMappingCone f)
          (topologicalMappingConeConeIncl f d))
    have hcollapse := ConcreteCategory.congr_hom
      (topologicalMappingConeConeIncl_collapse f) d
    change topologicalMappingConeCollapse f (topologicalMappingConeConeIncl f d) =
      topologicalSuspensionConeIncl A d at hcollapse
    rw [hcollapse, topologicalSecondHeightShrinkBottomAt_cone,
      topologicalSecondHeightShrinkOuterConeAt_base]
    exact (ConcreteCategory.congr_hom
      (topologicalMappingConeConeIncl_secondHeightShrinkAt f t 0) d).symm

/-- The fixed-time second-stage flattening on the whole iterated mapping cone. -/
def topologicalSecondHeightShrinkAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalMappingCone (topologicalMappingConeCollapse f) ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  pushout.desc
    (topologicalSecondHeightShrinkBottomAt f t)
    (topologicalSecondHeightShrinkOuterConeAt f t)
    (topologicalSecondHeightShrink_condition f t)

@[reassoc (attr := simp)]
theorem topologicalSecondMappingConeIncl_heightShrinkAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalMappingConeIncl (topologicalMappingConeCollapse f) ≫
        topologicalSecondHeightShrinkAt f t =
      topologicalSecondHeightShrinkBottomAt f t :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalSecondMappingConeConeIncl_heightShrinkAt
    (f : A ⟶ X) (t : TopCat.I) :
    topologicalMappingConeConeIncl (topologicalMappingConeCollapse f) ≫
        topologicalSecondHeightShrinkAt f t =
      topologicalSecondHeightShrinkOuterConeAt f t :=
  pushout.inr_desc _ _ _

/-- The outer-cylinder formula is jointly continuous in the second deformation time and the
outer-cylinder point. -/
theorem continuous_topologicalSecondHeightShrinkOuterCylinderAt_joint
    (f : A ⟶ X) :
    Continuous fun p : (TopCat.I.{u} : Type u) ×
        (topologicalMappingCone f ⊗ TopCat.I : TopCat.{u}) ↦
      topologicalSecondHeightShrinkOuterCylinderAt f p.1 p.2 := by
  have hreorder : Continuous fun p : (TopCat.I.{u} : Type u) ×
      (topologicalMappingCone f ⊗ TopCat.I : TopCat.{u}) ↦
        ((p.1, snd (topologicalMappingCone f) TopCat.I p.2),
          fst (topologicalMappingCone f) TopCat.I p.2) := by
    fun_prop
  have hcomp :=
    (continuous_topologicalSecondMappingConeHeightShrinkAt_joint f).comp hreorder
  convert hcomp using 1
  funext p
  rfl

/-- The outer-cone formula is jointly continuous in the second deformation time and the
outer-cone point. -/
theorem continuous_topologicalSecondHeightShrinkOuterConeAt_joint
    (f : A ⟶ X) :
    Continuous fun p : (TopCat.I.{u} : Type u) ×
        topologicalCone (topologicalMappingCone f) ↦
      topologicalSecondHeightShrinkOuterConeAt f p.1 p.2 := by
  apply (topologicalConeSumDesc_isQuotientMap
    (topologicalMappingCone f)).continuous_lift_prod_right
  let K :
      (((TopCat.I.{u} : Type u) ×
          (topologicalMappingCone f ⊗ TopCat.I : TopCat.{u})) ⊕
        ((TopCat.I.{u} : Type u) × (𝟙_ TopCat.{u}))) →
          topologicalMappingCone (topologicalMappingConeCollapse f) :=
    Sum.elim
      (fun p ↦ topologicalSecondHeightShrinkOuterCylinderAt f p.1 p.2)
      (fun _ ↦ topologicalSecondInnerHeightShrinkPoint f PUnit.unit)
  have hK : Continuous K := by
    rw [continuous_sum_dom]
    exact ⟨continuous_topologicalSecondHeightShrinkOuterCylinderAt_joint f,
      by dsimp [K]; fun_prop⟩
  have hcomp := hK.comp (Homeomorph.prodSumDistrib :
    (TopCat.I.{u} : Type u) ×
      ((topologicalMappingCone f ⊗ TopCat.I : TopCat.{u}) ⊕
        (𝟙_ TopCat.{u})) ≃ₜ _).continuous
  convert hcomp using 1
  funext p
  rcases p with ⟨t, c | z⟩
  · change topologicalSecondHeightShrinkOuterConeAt f t
        (topologicalConeCylinderIncl (topologicalMappingCone f) c) =
      K (Homeomorph.prodSumDistrib (t, Sum.inl c))
    rw [show (Homeomorph.prodSumDistrib (t, Sum.inl c) :
      (((TopCat.I.{u} : Type u) ×
          (topologicalMappingCone f ⊗ TopCat.I : TopCat.{u})) ⊕ _)) =
        Sum.inl (t, c) from rfl]
    dsimp [K]
    exact ConcreteCategory.congr_hom
      (topologicalSecondConeCylinderIncl_heightShrinkOuterConeAt f t) c
  · change topologicalSecondHeightShrinkOuterConeAt f t
        (topologicalConePointIncl (topologicalMappingCone f) z) =
      K (Homeomorph.prodSumDistrib (t, Sum.inr z))
    rw [show (Homeomorph.prodSumDistrib (t, Sum.inr z) :
      (((TopCat.I.{u} : Type u) ×
          (topologicalMappingCone f ⊗ TopCat.I : TopCat.{u})) ⊕ _)) =
        Sum.inr (t, z) from rfl]
    dsimp [K]
    exact ConcreteCategory.congr_hom
      (topologicalSecondConePointIncl_heightShrinkOuterConeAt f t) z

/-- The inner-cone formula at outer height zero is jointly continuous in deformation time and
the inner-cone point. -/
theorem continuous_topologicalSecondInnerHeightShrinkConeAt_zero_joint
    (f : A ⟶ X) :
    Continuous fun p : (TopCat.I.{u} : Type u) × topologicalCone A ↦
      topologicalSecondInnerHeightShrinkConeAt f p.1 0 p.2 := by
  have hembed : Continuous fun p :
      (TopCat.I.{u} : Type u) × topologicalCone A ↦
        ((p.1, (0 : TopCat.I.{u})), topologicalMappingConeConeIncl f p.2) := by
    fun_prop
  have hcomp :=
    (continuous_topologicalSecondMappingConeHeightShrinkAt_joint f).comp hembed
  convert hcomp using 1
  funext p
  exact (ConcreteCategory.congr_hom
    (topologicalMappingConeConeIncl_secondHeightShrinkAt f p.1 0) p.2).symm

/-- The bottom-suspension formula is jointly continuous in the second deformation time and the
suspension point. -/
theorem continuous_topologicalSecondHeightShrinkBottomAt_joint
    (f : A ⟶ X) :
    Continuous fun p : (TopCat.I.{u} : Type u) × topologicalSuspension A ↦
      topologicalSecondHeightShrinkBottomAt f p.1 p.2 := by
  apply (pushoutSumDesc_isQuotientMap (toUnit A)
    (topologicalConeBaseIncl A)).continuous_lift_prod_right
  let K :
      (((TopCat.I.{u} : Type u) × (𝟙_ TopCat.{u})) ⊕
        ((TopCat.I.{u} : Type u) × topologicalCone A)) →
          topologicalMappingCone (topologicalMappingConeCollapse f) :=
    Sum.elim
      (fun p ↦ topologicalMappingConeIncl (topologicalMappingConeCollapse f)
        (topologicalSuspensionPointIncl A p.2))
      (fun p ↦ topologicalSecondInnerHeightShrinkConeAt f p.1 0 p.2)
  have hK : Continuous K := by
    rw [continuous_sum_dom]
    exact ⟨by dsimp [K]; fun_prop,
      continuous_topologicalSecondInnerHeightShrinkConeAt_zero_joint f⟩
  have hcomp := hK.comp (Homeomorph.prodSumDistrib :
    (TopCat.I.{u} : Type u) ×
      ((𝟙_ TopCat.{u} : Type u) ⊕ topologicalCone A) ≃ₜ _).continuous
  convert hcomp using 1
  funext p
  rcases p with ⟨t, z | d⟩
  · change topologicalSecondHeightShrinkBottomAt f t
        (topologicalSuspensionPointIncl A z) =
      K (Homeomorph.prodSumDistrib (t, Sum.inl z))
    rw [show (Homeomorph.prodSumDistrib (t, Sum.inl z) :
      (((TopCat.I.{u} : Type u) × (𝟙_ TopCat.{u})) ⊕ _)) =
        Sum.inl (t, z) from rfl]
    dsimp [K]
    exact ConcreteCategory.congr_hom
      (topologicalSuspensionPointIncl_heightShrinkBottomAt f t) z
  · change topologicalSecondHeightShrinkBottomAt f t
        (topologicalSuspensionConeIncl A d) =
      K (Homeomorph.prodSumDistrib (t, Sum.inr d))
    rw [show (Homeomorph.prodSumDistrib (t, Sum.inr d) :
      (((TopCat.I.{u} : Type u) × (𝟙_ TopCat.{u})) ⊕ _)) =
        Sum.inr (t, d) from rfl]
    dsimp [K]
    exact ConcreteCategory.congr_hom
      (topologicalSuspensionConeIncl_heightShrinkBottomAt f t) d

/-- The second-stage flattening is jointly continuous in deformation time and in the entire
iterated mapping-cone variable. -/
theorem continuous_topologicalSecondHeightShrinkAt_joint
    (f : A ⟶ X) :
    Continuous fun p : (TopCat.I.{u} : Type u) ×
        topologicalMappingCone (topologicalMappingConeCollapse f) ↦
      topologicalSecondHeightShrinkAt f p.1 p.2 := by
  apply (pushoutSumDesc_isQuotientMap (topologicalMappingConeCollapse f)
    (topologicalConeBaseIncl (topologicalMappingCone f))).continuous_lift_prod_right
  let K :
      (((TopCat.I.{u} : Type u) × topologicalSuspension A) ⊕
        ((TopCat.I.{u} : Type u) ×
          topologicalCone (topologicalMappingCone f))) →
            topologicalMappingCone (topologicalMappingConeCollapse f) :=
    Sum.elim
      (fun p ↦ topologicalSecondHeightShrinkBottomAt f p.1 p.2)
      (fun p ↦ topologicalSecondHeightShrinkOuterConeAt f p.1 p.2)
  have hK : Continuous K := by
    rw [continuous_sum_dom]
    exact ⟨continuous_topologicalSecondHeightShrinkBottomAt_joint f,
      continuous_topologicalSecondHeightShrinkOuterConeAt_joint f⟩
  have hcomp := hK.comp (Homeomorph.prodSumDistrib :
    (TopCat.I.{u} : Type u) ×
      ((topologicalSuspension A : Type u) ⊕
        topologicalCone (topologicalMappingCone f)) ≃ₜ _).continuous
  convert hcomp using 1
  funext p
  rcases p with ⟨t, y | d⟩
  · change topologicalSecondHeightShrinkAt f t
        (topologicalMappingConeIncl (topologicalMappingConeCollapse f) y) =
      K (Homeomorph.prodSumDistrib (t, Sum.inl y))
    rw [show (Homeomorph.prodSumDistrib (t, Sum.inl y) :
      (((TopCat.I.{u} : Type u) × topologicalSuspension A) ⊕ _)) =
        Sum.inl (t, y) from rfl]
    dsimp [K]
    exact ConcreteCategory.congr_hom
      (topologicalSecondMappingConeIncl_heightShrinkAt f t) y
  · change topologicalSecondHeightShrinkAt f t
        (topologicalMappingConeConeIncl (topologicalMappingConeCollapse f) d) =
      K (Homeomorph.prodSumDistrib (t, Sum.inr d))
    rw [show (Homeomorph.prodSumDistrib (t, Sum.inr d) :
      (((TopCat.I.{u} : Type u) × topologicalSuspension A) ⊕ _)) =
        Sum.inr (t, d) from rfl]
    dsimp [K]
    exact ConcreteCategory.congr_hom
      (topologicalSecondMappingConeConeIncl_heightShrinkAt f t) d

/-- At time zero, the bottom-suspension part of the flattening is exactly the normalized bottom
map from the first deformation stage. -/
theorem topologicalSecondHeightShrinkBottomAt_zero
    (f : A ⟶ X) :
    topologicalSecondHeightShrinkBottomAt f 0 =
      topologicalSecondBottomHeightRaiseAt f 1 := by
  apply topologicalMappingCone_hom_ext (toUnit A)
  · simpa only [topologicalSuspensionPointIncl, topologicalSuspension] using
      (topologicalSuspensionPointIncl_heightShrinkBottomAt f 0).trans
        (topologicalSuspensionPointIncl_secondBottomHeightRaiseAt f 1).symm
  · apply topologicalCone_hom_ext A
    · apply TopCat.hom_ext
      ext p
      rcases p with ⟨a, u⟩
      change topologicalSecondHeightShrinkBottomAt f 0
          (topologicalSuspensionConeIncl A
            (topologicalConeCylinderIncl A (a, u))) =
        topologicalSecondBottomHeightRaiseAt f 1
          (topologicalSuspensionConeIncl A
            (topologicalConeCylinderIncl A (a, u)))
      rw [topologicalSecondHeightShrinkBottomAt_cone,
        topologicalSecondBottomHeightRaiseAt_cylinder]
      rw [show topologicalSecondInnerHeightShrinkConeAt f 0 0
          (topologicalConeCylinderIncl A (a, u)) =
        topologicalSecondInnerHeightShrinkCylinderAt f 0 0 (a, u) from
          ConcreteCategory.congr_hom
            (topologicalConeCylinderIncl_secondInnerHeightShrinkConeAt f 0 0)
            (a, u)]
      change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeCylinderIncl (topologicalMappingCone f)
            (topologicalMappingConeConeIncl f
                (topologicalConeCylinderIncl A
                  (a, TopCat.I.mul (u, TopCat.I.symm 0))),
              TopCat.I.max (0, u))) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeCylinderIncl (topologicalMappingCone f)
            (topologicalMappingConeConeIncl f
                (topologicalConeCylinderIncl A (a, u)),
              TopCat.I.mul (u, 1)))
      simp
    · apply TopCat.hom_ext
      ext z
      change topologicalSecondHeightShrinkBottomAt f 0
          (topologicalSuspensionConeIncl A (topologicalConePointIncl A z)) =
        topologicalSecondBottomHeightRaiseAt f 1
          (topologicalSuspensionConeIncl A (topologicalConePointIncl A z))
      rw [topologicalSecondHeightShrinkBottomAt_cone,
        topologicalSecondBottomHeightRaiseAt_apex]
      rw [show topologicalSecondInnerHeightShrinkConeAt f 0 0
          (topologicalConePointIncl A z) =
        topologicalSecondInnerHeightShrinkPoint f z from
          ConcreteCategory.congr_hom
            (topologicalConePointIncl_secondInnerHeightShrinkConeAt f 0 0) z]
      change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConePointIncl (topologicalMappingCone f) z) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeCylinderIncl (topologicalMappingCone f)
            (topologicalMappingConeConeIncl f (topologicalConePointIncl A z), 1))
      exact congrArg
        (topologicalMappingConeConeIncl (topologicalMappingConeCollapse f))
        (ConcreteCategory.congr_hom (pushout.condition :
          (TopCat.ι₁ : topologicalMappingCone f ⟶
              topologicalMappingCone f ⊗ TopCat.I) ≫
                topologicalConeCylinderIncl (topologicalMappingCone f) =
            toUnit (topologicalMappingCone f) ≫
              topologicalConePointIncl (topologicalMappingCone f))
          (topologicalMappingConeConeIncl f
            (topologicalConePointIncl A z))).symm

/-- At time zero, the fixed-outer-height flattening agrees with the first-stage normalization
on the corresponding outer cylinder. -/
theorem topologicalSecondMappingConeHeightShrinkAt_zero
    (f : A ⟶ X) (v : TopCat.I) :
    topologicalSecondMappingConeHeightShrinkAt f 0 v =
      lift (𝟙 (topologicalMappingCone f)) (TopCat.const v) ≫
        topologicalConeCylinderIncl (topologicalMappingCone f) ≫
          topologicalSecondConeHeightRaiseAt f 1 ≫
            topologicalMappingConeConeIncl
              (topologicalMappingConeCollapse f) := by
  apply topologicalMappingCone_hom_ext f
  · apply TopCat.hom_ext
    ext x
    change topologicalSecondMappingConeHeightShrinkAt f 0 v
        (topologicalMappingConeIncl f x) =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalSecondConeHeightRaiseAt f 1
          (topologicalConeCylinderIncl (topologicalMappingCone f)
            (topologicalMappingConeIncl f x, v)))
    have horiginal := ConcreteCategory.congr_hom
      (topologicalMappingConeIncl_secondHeightShrinkAt f 0 v) x
    change topologicalSecondMappingConeHeightShrinkAt f 0 v
        (topologicalMappingConeIncl f x) =
      topologicalSecondOriginalHeightShrinkAt f v x at horiginal
    rw [horiginal]
    exact congrArg
      (topologicalMappingConeConeIncl (topologicalMappingConeCollapse f))
      (topologicalSecondConeHeightRaiseAt_one_incl f x v).symm
  · apply topologicalCone_hom_ext A
    · apply TopCat.hom_ext
      ext p
      rcases p with ⟨a, u⟩
      change topologicalSecondMappingConeHeightShrinkAt f 0 v
          (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A (a, u))) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalSecondConeHeightRaiseAt f 1
            (topologicalConeCylinderIncl (topologicalMappingCone f)
              (topologicalMappingConeConeIncl f
                (topologicalConeCylinderIncl A (a, u)), v)))
      rw [show topologicalSecondMappingConeHeightShrinkAt f 0 v
          (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A (a, u))) =
        topologicalSecondInnerHeightShrinkConeAt f 0 v
          (topologicalConeCylinderIncl A (a, u)) from
          ConcreteCategory.congr_hom
            (topologicalMappingConeConeIncl_secondHeightShrinkAt f 0 v)
            (topologicalConeCylinderIncl A (a, u))]
      rw [show topologicalSecondInnerHeightShrinkConeAt f 0 v
          (topologicalConeCylinderIncl A (a, u)) =
        topologicalSecondInnerHeightShrinkCylinderAt f 0 v (a, u) from
          ConcreteCategory.congr_hom
            (topologicalConeCylinderIncl_secondInnerHeightShrinkConeAt f 0 v)
            (a, u)]
      change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeCylinderIncl (topologicalMappingCone f)
            (topologicalMappingConeConeIncl f
                (topologicalConeCylinderIncl A
                  (a, TopCat.I.mul (u, TopCat.I.symm 0))),
              TopCat.I.max (v, u))) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalSecondConeHeightRaiseAt f 1
            (topologicalConeCylinderIncl (topologicalMappingCone f)
              (topologicalMappingConeConeIncl f
                (topologicalConeCylinderIncl A (a, u)), v)))
      rw [TopCat.I.symm_zero, TopCat.I.mul_one_right]
      exact congrArg
        (topologicalMappingConeConeIncl (topologicalMappingConeCollapse f))
        (topologicalSecondConeHeightRaiseAt_one_doubleCylinder f a u v).symm
    · apply TopCat.hom_ext
      ext z
      change topologicalSecondMappingConeHeightShrinkAt f 0 v
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalSecondConeHeightRaiseAt f 1
            (topologicalConeCylinderIncl (topologicalMappingCone f)
              (topologicalMappingConeConeIncl f (topologicalConePointIncl A z), v)))
      rw [show topologicalSecondMappingConeHeightShrinkAt f 0 v
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
        topologicalSecondInnerHeightShrinkConeAt f 0 v
          (topologicalConePointIncl A z) from
          ConcreteCategory.congr_hom
            (topologicalMappingConeConeIncl_secondHeightShrinkAt f 0 v)
            (topologicalConePointIncl A z)]
      rw [show topologicalSecondInnerHeightShrinkConeAt f 0 v
          (topologicalConePointIncl A z) =
        topologicalSecondInnerHeightShrinkPoint f z from
          ConcreteCategory.congr_hom
            (topologicalConePointIncl_secondInnerHeightShrinkConeAt f 0 v) z]
      exact congrArg
        (topologicalMappingConeConeIncl (topologicalMappingConeCollapse f))
        (topologicalSecondConeHeightRaiseAt_one_innerApex f z v).symm

/-- At time zero, the outer-cone part of the flattening is the first-stage normalized outer
cone followed by its inclusion in the second mapping cone. -/
theorem topologicalSecondHeightShrinkOuterConeAt_zero
    (f : A ⟶ X) :
    topologicalSecondHeightShrinkOuterConeAt f 0 =
      topologicalSecondConeHeightRaiseAt f 1 ≫
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f) := by
  apply topologicalCone_hom_ext (topologicalMappingCone f)
  · apply TopCat.hom_ext
    ext p
    rcases p with ⟨c, v⟩
    change topologicalSecondHeightShrinkOuterConeAt f 0
        (topologicalConeCylinderIncl (topologicalMappingCone f) (c, v)) =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalSecondConeHeightRaiseAt f 1
          (topologicalConeCylinderIncl (topologicalMappingCone f) (c, v)))
    rw [show topologicalSecondHeightShrinkOuterConeAt f 0
        (topologicalConeCylinderIncl (topologicalMappingCone f) (c, v)) =
      topologicalSecondHeightShrinkOuterCylinderAt f 0 (c, v) from
        ConcreteCategory.congr_hom
          (topologicalSecondConeCylinderIncl_heightShrinkOuterConeAt f 0) (c, v)]
    exact ConcreteCategory.congr_hom
      (topologicalSecondMappingConeHeightShrinkAt_zero f v) c
  · rw [topologicalSecondConePointIncl_heightShrinkOuterConeAt,
      ← Category.assoc, topologicalSecondConePointIncl_heightRaiseAt]
    rfl

/-- The second-stage flattening starts exactly at the normalized endpoint of the first-stage
height-raising homotopy. -/
theorem topologicalSecondHeightShrinkAt_zero
    (f : A ⟶ X) :
    topologicalSecondHeightShrinkAt f 0 =
      topologicalSecondHeightRaiseAt f 1 := by
  apply topologicalMappingCone_hom_ext (topologicalMappingConeCollapse f)
  · rw [topologicalSecondMappingConeIncl_heightShrinkAt,
      topologicalSecondMappingConeIncl_heightRaiseAt,
      topologicalSecondHeightShrinkBottomAt_zero]
  · rw [topologicalSecondMappingConeConeIncl_heightShrinkAt,
      topologicalSecondMappingConeConeIncl_heightRaiseAt,
      topologicalSecondHeightShrinkOuterConeAt_zero]

/-- The underlying two-variable function of the second-stage flattening homotopy. -/
def topologicalSecondHeightShrinkHomotopyToFun
    (f : A ⟶ X) :
    unitInterval ×
        topologicalMappingCone (topologicalMappingConeCollapse f) →
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  fun p ↦ topologicalSecondHeightShrinkAt f
    (TopCat.I.homeomorph.symm p.1) p.2

theorem continuous_topologicalSecondHeightShrinkHomotopyToFun
    (f : A ⟶ X) :
    Continuous (topologicalSecondHeightShrinkHomotopyToFun f) := by
  unfold topologicalSecondHeightShrinkHomotopyToFun
  let e : unitInterval ×
      topologicalMappingCone (topologicalMappingConeCollapse f) →
        (TopCat.I.{u} : Type u) ×
          topologicalMappingCone (topologicalMappingConeCollapse f) :=
    fun p ↦ (TopCat.I.homeomorph.symm p.1, p.2)
  have he : Continuous e := by
    dsimp [e]
    fun_prop
  have h := (continuous_topologicalSecondHeightShrinkAt_joint f).comp he
  convert h using 1
  funext p
  rfl

@[simp]
theorem topologicalSecondHeightShrinkHomotopyToFun_zero
    (f : A ⟶ X)
    (z : topologicalMappingCone (topologicalMappingConeCollapse f)) :
    topologicalSecondHeightShrinkHomotopyToFun f (0, z) =
      topologicalSecondHeightRaiseAt f 1 z := by
  change topologicalSecondHeightShrinkAt f 0 z =
    topologicalSecondHeightRaiseAt f 1 z
  exact ConcreteCategory.congr_hom
    (topologicalSecondHeightShrinkAt_zero f) z

@[simp]
theorem topologicalSecondHeightShrinkHomotopyToFun_one
    (f : A ⟶ X)
    (z : topologicalMappingCone (topologicalMappingConeCollapse f)) :
    topologicalSecondHeightShrinkHomotopyToFun f (1, z) =
      topologicalSecondHeightShrinkAt f 1 z := by
  rfl

/-- The second-stage flattening as a homotopy from the first-stage normalized endpoint to its
time-one flattening. -/
def topologicalSecondHeightShrinkHomotopy
    (f : A ⟶ X) :
    TopCat.Homotopy
      (topologicalSecondHeightRaiseAt f 1)
      (topologicalSecondHeightShrinkAt f 1) where
  toFun := topologicalSecondHeightShrinkHomotopyToFun f
  continuous_toFun := continuous_topologicalSecondHeightShrinkHomotopyToFun f
  map_zero_left := topologicalSecondHeightShrinkHomotopyToFun_zero f
  map_one_left := topologicalSecondHeightShrinkHomotopyToFun_one f

/-- At time one, the bottom-suspension flattening is the bottom restriction of the comparison
composite through `ΣX`. -/
theorem topologicalSecondHeightShrinkBottomAt_one
    (f : A ⟶ X) :
    topologicalSecondHeightShrinkBottomAt f 1 =
      topologicalSuspensionMap A f ≫
        topologicalSuspensionToSecondMappingCone f := by
  apply topologicalMappingCone_hom_ext (toUnit A)
  · change topologicalSuspensionPointIncl A ≫
        topologicalSecondHeightShrinkBottomAt f 1 =
      (topologicalSuspensionPointIncl A ≫ topologicalSuspensionMap A f) ≫
        topologicalSuspensionToSecondMappingCone f
    rw [topologicalSuspensionPointIncl_heightShrinkBottomAt,
      topologicalSuspensionPointIncl_map,
      topologicalSuspensionPointIncl_toSecondMappingCone]
  · apply topologicalCone_hom_ext A
    · apply TopCat.hom_ext
      ext p
      rcases p with ⟨a, u⟩
      change topologicalSecondHeightShrinkBottomAt f 1
          (topologicalSuspensionConeIncl A
            (topologicalConeCylinderIncl A (a, u))) =
        topologicalSuspensionToSecondMappingCone f
          (topologicalSuspensionMap A f
            (topologicalSuspensionConeIncl A
              (topologicalConeCylinderIncl A (a, u))))
      rw [topologicalSecondHeightShrinkBottomAt_cone]
      rw [show topologicalSecondInnerHeightShrinkConeAt f 1 0
          (topologicalConeCylinderIncl A (a, u)) =
        topologicalSecondInnerHeightShrinkCylinderAt f 1 0 (a, u) from
          ConcreteCategory.congr_hom
            (topologicalConeCylinderIncl_secondInnerHeightShrinkConeAt f 1 0)
            (a, u)]
      have hsusp := ConcreteCategory.congr_hom
        (topologicalSuspensionConeIncl_map A f)
        (topologicalConeCylinderIncl A (a, u))
      change topologicalSuspensionMap A f
          (topologicalSuspensionConeIncl A
            (topologicalConeCylinderIncl A (a, u))) =
        topologicalSuspensionConeIncl X
          (topologicalConeMap f (topologicalConeCylinderIncl A (a, u))) at hsusp
      rw [hsusp]
      have hsection := ConcreteCategory.congr_hom
        (topologicalSuspensionConeIncl_toSecondMappingCone f)
        (topologicalConeMap f (topologicalConeCylinderIncl A (a, u)))
      change topologicalSuspensionToSecondMappingCone f
          (topologicalSuspensionConeIncl X
            (topologicalConeMap f (topologicalConeCylinderIncl A (a, u)))) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeMap (topologicalMappingConeIncl f)
            (topologicalConeMap f (topologicalConeCylinderIncl A (a, u)))) at hsection
      rw [hsection]
      have hfCylinder := ConcreteCategory.congr_hom
        (topologicalConeCylinderIncl_map f) (a, u)
      change topologicalConeMap f (topologicalConeCylinderIncl A (a, u)) =
        topologicalConeCylinderIncl X (f a, u) at hfCylinder
      rw [hfCylinder]
      have hinclCylinder := ConcreteCategory.congr_hom
        (topologicalConeCylinderIncl_map (topologicalMappingConeIncl f)) (f a, u)
      change topologicalConeMap (topologicalMappingConeIncl f)
          (topologicalConeCylinderIncl X (f a, u)) =
        topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeIncl f (f a), u) at hinclCylinder
      rw [hinclCylinder]
      change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeCylinderIncl (topologicalMappingCone f)
            (topologicalMappingConeConeIncl f
                (topologicalConeCylinderIncl A
                  (a, TopCat.I.mul (u, TopCat.I.symm 1))),
              TopCat.I.max (0, u))) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeCylinderIncl (topologicalMappingCone f)
            (topologicalMappingConeIncl f (f a), u))
      rw [TopCat.I.symm_one, TopCat.I.mul_zero_right,
        TopCat.I.max_zero_left]
      have hinner := ConcreteCategory.congr_hom
        (topologicalMappingCone_condition f) a
      change topologicalMappingConeIncl f (f a) =
        topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A (a, 0)) at hinner
      rw [hinner]
    · apply TopCat.hom_ext
      ext z
      change topologicalSecondHeightShrinkBottomAt f 1
          (topologicalSuspensionConeIncl A (topologicalConePointIncl A z)) =
        topologicalSuspensionToSecondMappingCone f
          (topologicalSuspensionMap A f
            (topologicalSuspensionConeIncl A (topologicalConePointIncl A z)))
      rw [topologicalSecondHeightShrinkBottomAt_cone]
      rw [show topologicalSecondInnerHeightShrinkConeAt f 1 0
          (topologicalConePointIncl A z) =
        topologicalSecondInnerHeightShrinkPoint f z from
          ConcreteCategory.congr_hom
            (topologicalConePointIncl_secondInnerHeightShrinkConeAt f 1 0) z]
      have hsusp := ConcreteCategory.congr_hom
        (topologicalSuspensionConeIncl_map A f) (topologicalConePointIncl A z)
      change topologicalSuspensionMap A f
          (topologicalSuspensionConeIncl A (topologicalConePointIncl A z)) =
        topologicalSuspensionConeIncl X
          (topologicalConeMap f (topologicalConePointIncl A z)) at hsusp
      rw [hsusp]
      have hsection := ConcreteCategory.congr_hom
        (topologicalSuspensionConeIncl_toSecondMappingCone f)
        (topologicalConeMap f (topologicalConePointIncl A z))
      change topologicalSuspensionToSecondMappingCone f
          (topologicalSuspensionConeIncl X
            (topologicalConeMap f (topologicalConePointIncl A z))) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeMap (topologicalMappingConeIncl f)
            (topologicalConeMap f (topologicalConePointIncl A z))) at hsection
      rw [hsection]
      have hfPoint := ConcreteCategory.congr_hom
        (topologicalConePointIncl_map f) z
      change topologicalConeMap f (topologicalConePointIncl A z) =
        topologicalConePointIncl X z at hfPoint
      rw [hfPoint]
      have hinclPoint := ConcreteCategory.congr_hom
        (topologicalConePointIncl_map (topologicalMappingConeIncl f)) z
      change topologicalConeMap (topologicalMappingConeIncl f)
          (topologicalConePointIncl X z) =
        topologicalConePointIncl (topologicalMappingCone f) z at hinclPoint
      rw [hinclPoint]
      rfl

/-- At time one and fixed outer height, flattening agrees with first mapping into the target
cone, radially contracting by the outer height, and then applying the section cone map. -/
theorem topologicalSecondMappingConeHeightShrinkAt_time_one
    (f : A ⟶ X) (v : TopCat.I) :
    topologicalSecondMappingConeHeightShrinkAt f 1 v =
      topologicalMappingConeToCone f ≫
        topologicalConeContractAt X v ≫
          topologicalConeMap (topologicalMappingConeIncl f) ≫
            topologicalMappingConeConeIncl
              (topologicalMappingConeCollapse f) := by
  apply topologicalMappingCone_hom_ext f
  · apply TopCat.hom_ext
    ext x
    change topologicalSecondMappingConeHeightShrinkAt f 1 v
        (topologicalMappingConeIncl f x) =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeMap (topologicalMappingConeIncl f)
          (topologicalConeContractAt X v
            (topologicalMappingConeToCone f (topologicalMappingConeIncl f x))))
    have horiginal := ConcreteCategory.congr_hom
      (topologicalMappingConeIncl_secondHeightShrinkAt f 1 v) x
    change topologicalSecondMappingConeHeightShrinkAt f 1 v
        (topologicalMappingConeIncl f x) =
      topologicalSecondOriginalHeightShrinkAt f v x at horiginal
    rw [horiginal]
    have htoCone := ConcreteCategory.congr_hom
      (topologicalMappingConeIncl_toCone f) x
    change topologicalMappingConeToCone f (topologicalMappingConeIncl f x) =
      topologicalConeBaseIncl X x at htoCone
    rw [htoCone]
    change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeIncl f x, v)) =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeMap (topologicalMappingConeIncl f)
          (topologicalConeContractAt X v (topologicalConeBaseIncl X x)))
    rw [show topologicalConeBaseIncl X x =
      topologicalConeCylinderIncl X (x, 0) from rfl]
    have hcontract := ConcreteCategory.congr_hom
      (topologicalConeCylinderIncl_contractAt X v) (x, (0 : TopCat.I.{u}))
    change topologicalConeContractAt X v
        (topologicalConeCylinderIncl X (x, 0)) =
      topologicalConeCylinderIncl X (x, TopCat.I.max (0, v)) at hcontract
    rw [hcontract, TopCat.I.max_zero_left]
    have hmap := ConcreteCategory.congr_hom
      (topologicalConeCylinderIncl_map (topologicalMappingConeIncl f)) (x, v)
    change topologicalConeMap (topologicalMappingConeIncl f)
        (topologicalConeCylinderIncl X (x, v)) =
      topologicalConeCylinderIncl (topologicalMappingCone f)
        (topologicalMappingConeIncl f x, v) at hmap
    rw [hmap]
  · apply topologicalCone_hom_ext A
    · apply TopCat.hom_ext
      ext p
      rcases p with ⟨a, u⟩
      change topologicalSecondMappingConeHeightShrinkAt f 1 v
          (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A (a, u))) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeMap (topologicalMappingConeIncl f)
            (topologicalConeContractAt X v
              (topologicalMappingConeToCone f
                (topologicalMappingConeConeIncl f
                  (topologicalConeCylinderIncl A (a, u))))))
      rw [show topologicalSecondMappingConeHeightShrinkAt f 1 v
          (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A (a, u))) =
        topologicalSecondInnerHeightShrinkConeAt f 1 v
          (topologicalConeCylinderIncl A (a, u)) from
          ConcreteCategory.congr_hom
            (topologicalMappingConeConeIncl_secondHeightShrinkAt f 1 v)
            (topologicalConeCylinderIncl A (a, u))]
      rw [show topologicalSecondInnerHeightShrinkConeAt f 1 v
          (topologicalConeCylinderIncl A (a, u)) =
        topologicalSecondInnerHeightShrinkCylinderAt f 1 v (a, u) from
          ConcreteCategory.congr_hom
            (topologicalConeCylinderIncl_secondInnerHeightShrinkConeAt f 1 v)
            (a, u)]
      have htoCone := ConcreteCategory.congr_hom
        (topologicalMappingConeConeIncl_toCone f)
        (topologicalConeCylinderIncl A (a, u))
      change topologicalMappingConeToCone f
          (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A (a, u))) =
        topologicalConeMap f (topologicalConeCylinderIncl A (a, u)) at htoCone
      rw [htoCone]
      have hfMap := ConcreteCategory.congr_hom
        (topologicalConeCylinderIncl_map f) (a, u)
      change topologicalConeMap f (topologicalConeCylinderIncl A (a, u)) =
        topologicalConeCylinderIncl X (f a, u) at hfMap
      rw [hfMap]
      have hcontract := ConcreteCategory.congr_hom
        (topologicalConeCylinderIncl_contractAt X v) (f a, u)
      change topologicalConeContractAt X v
          (topologicalConeCylinderIncl X (f a, u)) =
        topologicalConeCylinderIncl X (f a, TopCat.I.max (u, v)) at hcontract
      rw [hcontract]
      have hinclMap := ConcreteCategory.congr_hom
        (topologicalConeCylinderIncl_map (topologicalMappingConeIncl f))
        (f a, TopCat.I.max (u, v))
      change topologicalConeMap (topologicalMappingConeIncl f)
          (topologicalConeCylinderIncl X (f a, TopCat.I.max (u, v))) =
        topologicalConeCylinderIncl (topologicalMappingCone f)
          (topologicalMappingConeIncl f (f a), TopCat.I.max (u, v)) at hinclMap
      rw [hinclMap]
      change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeCylinderIncl (topologicalMappingCone f)
            (topologicalMappingConeConeIncl f
                (topologicalConeCylinderIncl A
                  (a, TopCat.I.mul (u, TopCat.I.symm 1))),
              TopCat.I.max (v, u))) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeCylinderIncl (topologicalMappingCone f)
            (topologicalMappingConeIncl f (f a), TopCat.I.max (u, v)))
      rw [TopCat.I.symm_one, TopCat.I.mul_zero_right,
        TopCat.I.max_comm]
      have hinner := ConcreteCategory.congr_hom
        (topologicalMappingCone_condition f) a
      change topologicalMappingConeIncl f (f a) =
        topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A (a, 0)) at hinner
      rw [hinner]
    · apply TopCat.hom_ext
      ext z
      change topologicalSecondMappingConeHeightShrinkAt f 1 v
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
          (topologicalConeMap (topologicalMappingConeIncl f)
            (topologicalConeContractAt X v
              (topologicalMappingConeToCone f
                (topologicalMappingConeConeIncl f
                  (topologicalConePointIncl A z)))))
      rw [show topologicalSecondMappingConeHeightShrinkAt f 1 v
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
        topologicalSecondInnerHeightShrinkConeAt f 1 v
          (topologicalConePointIncl A z) from
          ConcreteCategory.congr_hom
            (topologicalMappingConeConeIncl_secondHeightShrinkAt f 1 v)
            (topologicalConePointIncl A z)]
      rw [show topologicalSecondInnerHeightShrinkConeAt f 1 v
          (topologicalConePointIncl A z) =
        topologicalSecondInnerHeightShrinkPoint f z from
          ConcreteCategory.congr_hom
            (topologicalConePointIncl_secondInnerHeightShrinkConeAt f 1 v) z]
      have htoCone := ConcreteCategory.congr_hom
        (topologicalMappingConeConeIncl_toCone f) (topologicalConePointIncl A z)
      change topologicalMappingConeToCone f
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
        topologicalConeMap f (topologicalConePointIncl A z) at htoCone
      rw [htoCone]
      have hfPoint := ConcreteCategory.congr_hom
        (topologicalConePointIncl_map f) z
      change topologicalConeMap f (topologicalConePointIncl A z) =
        topologicalConePointIncl X z at hfPoint
      rw [hfPoint]
      have hcontract := ConcreteCategory.congr_hom
        (topologicalConePointIncl_contractAt X v) z
      change topologicalConeContractAt X v (topologicalConePointIncl X z) =
        topologicalConePointIncl X z at hcontract
      rw [hcontract]
      have hinclPoint := ConcreteCategory.congr_hom
        (topologicalConePointIncl_map (topologicalMappingConeIncl f)) z
      change topologicalConeMap (topologicalMappingConeIncl f)
          (topologicalConePointIncl X z) =
        topologicalConePointIncl (topologicalMappingCone f) z at hinclPoint
      rw [hinclPoint]
      rfl

/-- At time one, the outer-cone flattening is the outer-cone restriction of the comparison
composite through `ΣX`. -/
theorem topologicalSecondHeightShrinkOuterConeAt_one
    (f : A ⟶ X) :
    topologicalSecondHeightShrinkOuterConeAt f 1 =
      topologicalConeExtensionOfNullhomotopy
          (topologicalMappingConeCollapse f ≫ topologicalSuspensionMap A f)
          (topologicalConePointIncl X ≫ topologicalSuspensionConeIncl X)
          (topologicalMappingConeCollapseSuspensionRadialNullhomotopy f) ≫
        topologicalSuspensionToSecondMappingCone f := by
  apply topologicalCone_hom_ext (topologicalMappingCone f)
  · rw [topologicalSecondConeCylinderIncl_heightShrinkOuterConeAt,
      ← Category.assoc,
      topologicalConeCylinderIncl_extensionOfNullhomotopy_h]
    apply TopCat.hom_ext
    ext p
    rcases p with ⟨c, v⟩
    change topologicalSecondMappingConeHeightShrinkAt f 1 v c =
      topologicalSuspensionToSecondMappingCone f
        ((topologicalMappingConeCollapseSuspensionRadialNullhomotopy f).h (c, v))
    rw [show topologicalSecondMappingConeHeightShrinkAt f 1 v c =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeMap (topologicalMappingConeIncl f)
          (topologicalConeContractAt X v (topologicalMappingConeToCone f c))) from
        ConcreteCategory.congr_hom
          (topologicalSecondMappingConeHeightShrinkAt_time_one f v) c]
    rw [TopCat.Homotopy.h_hom_apply]
    change topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeMap (topologicalMappingConeIncl f)
          (topologicalConeContractAt X v (topologicalMappingConeToCone f c))) =
      topologicalSuspensionToSecondMappingCone f
        (topologicalSuspensionConeIncl X
          (topologicalConeContractAt X
            (TopCat.I.homeomorph.symm (TopCat.I.homeomorph v))
            (topologicalMappingConeToCone f c)))
    rw [TopCat.I.homeomorph.symm_apply_apply]
    have hsection := ConcreteCategory.congr_hom
      (topologicalSuspensionConeIncl_toSecondMappingCone f)
      (topologicalConeContractAt X v (topologicalMappingConeToCone f c))
    change topologicalSuspensionToSecondMappingCone f
        (topologicalSuspensionConeIncl X
          (topologicalConeContractAt X v (topologicalMappingConeToCone f c))) =
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)
        (topologicalConeMap (topologicalMappingConeIncl f)
          (topologicalConeContractAt X v (topologicalMappingConeToCone f c))) at hsection
    exact hsection.symm
  · rw [topologicalSecondConePointIncl_heightShrinkOuterConeAt,
      ← Category.assoc, topologicalConePointIncl_extensionOfNullhomotopy,
      Category.assoc, topologicalSuspensionConeIncl_toSecondMappingCone,
      ← Category.assoc, topologicalConePointIncl_map]
    rfl

/-- The time-one flattening is exactly the composite of the canonical comparison to `ΣX` and
its strict section back to the second mapping cone. -/
theorem topologicalSecondHeightShrinkAt_one
    (f : A ⟶ X) :
    topologicalSecondHeightShrinkAt f 1 =
      topologicalSecondMappingConeToSuspension f ≫
        topologicalSuspensionToSecondMappingCone f := by
  apply topologicalMappingCone_hom_ext (topologicalMappingConeCollapse f)
  · rw [topologicalSecondMappingConeIncl_heightShrinkAt,
      ← Category.assoc, topologicalSecondMappingConeIncl_toSuspension,
      topologicalSecondHeightShrinkBottomAt_one]
  · rw [topologicalSecondMappingConeConeIncl_heightShrinkAt,
      ← Category.assoc, topologicalSecondMappingConeConeIncl_toSuspension,
      topologicalSecondHeightShrinkOuterConeAt_one]

/-- The identity of the second mapping cone is homotopic to the composite through `ΣX`. -/
noncomputable def topologicalSecondComparisonCompositeHomotopy
    (f : A ⟶ X) :
    TopCat.Homotopy
      (𝟙 (topologicalMappingCone (topologicalMappingConeCollapse f)))
      (topologicalSecondMappingConeToSuspension f ≫
        topologicalSuspensionToSecondMappingCone f) := by
  rw [← topologicalSecondHeightShrinkAt_one]
  exact (topologicalSecondHeightRaiseHomotopy f).trans
    (topologicalSecondHeightShrinkHomotopy f)

/-- The canonical Puppe comparison identifies the mapping cone of `C_f → ΣA` with `ΣX` up to
homotopy.  Its inverse is the explicit strict section constructed from the suspension pushout. -/
noncomputable def topologicalSecondMappingConeHomotopyEquivSuspension
    (f : A ⟶ X) :
    ContinuousMap.HomotopyEquiv
      (topologicalMappingCone (topologicalMappingConeCollapse f) : Type u)
      (topologicalSuspension X : Type u) where
  toFun := (topologicalSecondMappingConeToSuspension f).hom
  invFun := (topologicalSuspensionToSecondMappingCone f).hom
  left_inv := by
    exact ⟨(topologicalSecondComparisonCompositeHomotopy f).symm⟩
  right_inv := by
    rw [show (topologicalSecondMappingConeToSuspension f).hom.comp
        (topologicalSuspensionToSecondMappingCone f).hom =
      (topologicalSuspensionToSecondMappingCone f ≫
        topologicalSecondMappingConeToSuspension f).hom from rfl,
      topologicalSuspensionToSecondMappingCone_toSuspension]
    exact ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id _)⟩

end Submission
