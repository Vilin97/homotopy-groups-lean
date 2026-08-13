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

end Submission
