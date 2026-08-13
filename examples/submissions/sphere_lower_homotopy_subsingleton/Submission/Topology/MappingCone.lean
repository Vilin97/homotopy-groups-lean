/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.PushoutMono
import Submission.Topology.Interval
import Mathlib.Topology.Homotopy.Contractible
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

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory CartesianMonoidalCategory

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

/-- The quotient map from the disjoint union of the cylinder and cone point onto the cone. -/
def topologicalConeSumDesc (A : TopCat.{u}) :
    ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u})) → topologicalCone A :=
  pushoutSumDesc (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) (toUnit A)

theorem topologicalConeSumDesc_isQuotientMap (A : TopCat.{u}) :
    IsQuotientMap (topologicalConeSumDesc A) :=
  pushoutSumDesc_isQuotientMap _ _

/-- The inclusion of the base `A × {0}` into the cone. -/
def topologicalConeBaseIncl (A : TopCat.{u}) : A ⟶ topologicalCone A :=
  TopCat.ι₀ ≫ topologicalConeCylinderIncl A

/-- The base embeds in the topological cone.  Although the cone quotient identifies every
point at the `1`-end of the cylinder, it makes no identifications at the disjoint `0`-end. -/
instance (A : TopCat.{u}) : Mono (topologicalConeBaseIncl A) := by
  rw [TopCat.mono_iff_injective]
  intro x y hxy
  let f := (forget TopCat).map (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I)
  let g := (forget TopCat).map (toUnit A)
  letI : Mono f := (CategoryTheory.mono_iff_injective f).mpr (by
    intro x y h
    exact congrArg Prod.fst h)
  have hpo := (IsPushout.of_isColimit
    (pushoutIsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) (toUnit A))).map (forget TopCat)
  let e : hpo.cocone ≅ Types.Pushout.cocone f g := Cocone.ext
    (IsColimit.coconePointUniqueUpToIso hpo.isColimit
      (Types.Pushout.isColimitCocone f g)) (by simp)
  have hxy' :
      (Types.Pushout.cocone f g).inl ((forget TopCat).map TopCat.ι₀ x) =
      (Types.Pushout.cocone f g).inl ((forget TopCat).map TopCat.ι₀ y) := by
    change hpo.cocone.inl ((forget TopCat).map TopCat.ι₀ x) =
      hpo.cocone.inl ((forget TopCat).map TopCat.ι₀ y) at hxy
    convert! congr_arg e.hom.hom hxy
    · exact ConcreteCategory.congr_hom (e.hom.w WalkingSpan.left).symm _
    · exact ConcreteCategory.congr_hom (e.hom.w WalkingSpan.left).symm _
  have hr : Types.Pushout.Rel' f g
      (Sum.inl ((forget TopCat).map TopCat.ι₀ x))
      (Sum.inl ((forget TopCat).map TopCat.ι₀ y)) :=
    (Types.Pushout.quot_mk_eq_iff f g _ _).mp hxy'
  rw [Types.Pushout.inl_rel'_inl_iff] at hr
  rcases hr with h | ⟨x₀, y₀, h₀, hx, hy⟩
  · exact congrArg Prod.fst h
  · have hz : (0 : TopCat.I.{u}) = 1 := congrArg Prod.snd hx
    have hz' := congrArg TopCat.I.homeomorph hz
    norm_num at hz'

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

/-- Maps out of a cone are determined by their restrictions to the cylinder and cone point. -/
theorem topologicalCone_hom_ext (A : TopCat.{u}) {Y : TopCat.{u}}
    {f g : topologicalCone A ⟶ Y}
    (hC : topologicalConeCylinderIncl A ≫ f = topologicalConeCylinderIncl A ≫ g)
    (hP : topologicalConePointIncl A ≫ f = topologicalConePointIncl A ≫ g) : f = g :=
  pushout.hom_ext hC hP

/-- The height coordinate on a cone, equal to the cylinder coordinate and equal to one at the
cone point. -/
def topologicalConeHeight (A : TopCat.{u}) : topologicalCone A ⟶ TopCat.I :=
  topologicalConeDesc A (snd A TopCat.I) (TopCat.const 1) (by
    rw [TopCat.ι₁_snd]
    rfl)

@[reassoc (attr := simp)]
theorem topologicalConeCylinderIncl_height (A : TopCat.{u}) :
    topologicalConeCylinderIncl A ≫ topologicalConeHeight A = snd A TopCat.I := by
  rw [topologicalConeHeight, topologicalConeCylinderIncl_desc]

@[reassoc (attr := simp)]
theorem topologicalConePointIncl_height (A : TopCat.{u}) :
    topologicalConePointIncl A ≫ topologicalConeHeight A = TopCat.const 1 := by
  rw [topologicalConeHeight, topologicalConePointIncl_desc]

@[reassoc (attr := simp)]
theorem topologicalConeBaseIncl_height (A : TopCat.{u}) :
    topologicalConeBaseIncl A ≫ topologicalConeHeight A = TopCat.const 0 := by
  rw [topologicalConeBaseIncl, Category.assoc,
    topologicalConeCylinderIncl_height, TopCat.ι₀_snd]

/-! ### Contracting the cone toward its apex -/

/-- Raise a cylinder point toward the cone end by taking the maximum of its height and `t`. -/
def topologicalConeRaiseAt (A : TopCat.{u}) (t : TopCat.I) :
    A ⊗ TopCat.I ⟶ A ⊗ TopCat.I :=
  lift (fst A TopCat.I)
    (lift (snd A TopCat.I) (TopCat.const t) ≫ TopCat.I.max)

@[simp]
theorem topologicalConeRaiseAt_apply (A : TopCat.{u}) (t : TopCat.I)
    (a : A) (s : TopCat.I) :
    topologicalConeRaiseAt A t (a, s) = (a, TopCat.I.max (s, t)) := rfl

@[reassoc (attr := simp)]
theorem topologicalCone_ι₁_raiseAt (A : TopCat.{u}) (t : TopCat.I) :
    TopCat.ι₁ ≫ topologicalConeRaiseAt A t = TopCat.ι₁ := by
  apply TopCat.hom_ext
  ext a
  simp

@[simp]
theorem topologicalConeRaiseAt_zero (A : TopCat.{u}) :
    topologicalConeRaiseAt A 0 = 𝟙 (A ⊗ TopCat.I) := by
  apply TopCat.hom_ext
  ext p
  rcases p with ⟨a, s⟩
  simp

theorem topologicalConeRaiseAt_one_cylinder (A : TopCat.{u}) :
    topologicalConeRaiseAt A 1 ≫ topologicalConeCylinderIncl A =
      toUnit (A ⊗ TopCat.I) ≫ topologicalConePointIncl A := by
  apply TopCat.hom_ext
  ext p
  rcases p with ⟨a, s⟩
  change topologicalConeCylinderIncl A (a, TopCat.I.max (s, 1)) =
    topologicalConePointIncl A (toUnit (A ⊗ TopCat.I) (a, s))
  rw [TopCat.I.max_one_right]
  exact ConcreteCategory.congr_hom (pushout.condition :
    (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) ≫ topologicalConeCylinderIncl A =
      toUnit A ≫ topologicalConePointIncl A) a

/-- The time-`t` map in the contraction of a cone toward its apex. -/
def topologicalConeContractAt (A : TopCat.{u}) (t : TopCat.I) :
    topologicalCone A ⟶ topologicalCone A :=
  topologicalConeDesc A
    (topologicalConeRaiseAt A t ≫ topologicalConeCylinderIncl A)
    (topologicalConePointIncl A) (by
      rw [← Category.assoc, topologicalCone_ι₁_raiseAt]
      exact pushout.condition)

@[reassoc (attr := simp)]
theorem topologicalConeCylinderIncl_contractAt (A : TopCat.{u}) (t : TopCat.I) :
    topologicalConeCylinderIncl A ≫ topologicalConeContractAt A t =
      topologicalConeRaiseAt A t ≫ topologicalConeCylinderIncl A := by
  rw [topologicalConeContractAt, topologicalConeCylinderIncl_desc]

@[reassoc (attr := simp)]
theorem topologicalConePointIncl_contractAt (A : TopCat.{u}) (t : TopCat.I) :
    topologicalConePointIncl A ≫ topologicalConeContractAt A t =
      topologicalConePointIncl A := by
  rw [topologicalConeContractAt, topologicalConePointIncl_desc]

@[simp]
theorem topologicalConeContractAt_zero (A : TopCat.{u}) :
    topologicalConeContractAt A 0 = 𝟙 (topologicalCone A) := by
  apply topologicalCone_hom_ext A
  · rw [topologicalConeCylinderIncl_contractAt, topologicalConeRaiseAt_zero,
      Category.id_comp, Category.comp_id]
  · rw [topologicalConePointIncl_contractAt, Category.comp_id]

@[simp]
theorem topologicalConeContractAt_one (A : TopCat.{u}) :
    topologicalConeContractAt A 1 =
      toUnit (topologicalCone A) ≫ topologicalConePointIncl A := by
  apply topologicalCone_hom_ext A
  · rw [topologicalConeCylinderIncl_contractAt,
      topologicalConeRaiseAt_one_cylinder]
    rfl
  · rw [topologicalConePointIncl_contractAt]
    rfl

/-- The contraction of the topological cone from the identity to its cone point. -/
def topologicalConeContractHomotopy (A : TopCat.{u}) :
    TopCat.Homotopy (𝟙 (topologicalCone A))
      (toUnit (topologicalCone A) ≫ topologicalConePointIncl A) where
  toFun p := topologicalConeContractAt A (TopCat.I.homeomorph.symm p.1) p.2
  continuous_toFun := by
    apply (pushoutSumDesc_isQuotientMap
      (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) (toUnit A)).continuous_lift_prod_right
    let K : ((unitInterval × (A ⊗ TopCat.I : TopCat.{u})) ⊕
        (unitInterval × (𝟙_ TopCat.{u}))) → topologicalCone A :=
      Sum.elim
        (fun p ↦ topologicalConeCylinderIncl A
          (fst A TopCat.I p.2,
            TopCat.I.max (snd A TopCat.I p.2, TopCat.I.homeomorph.symm p.1)))
        (fun p ↦ topologicalConePointIncl A p.2)
    have hK : Continuous K := by
      rw [continuous_sum_dom]
      constructor <;> dsimp [K] <;> fun_prop
    have hcomp := hK.comp (Homeomorph.prodSumDistrib :
      unitInterval × ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u})) ≃ₜ _).continuous
    convert hcomp using 1
    funext p
    rcases p with ⟨t, c | z⟩
    · change topologicalConeContractAt A (TopCat.I.homeomorph.symm t)
        (topologicalConeCylinderIncl A c) = _
      exact ConcreteCategory.congr_hom
        (topologicalConeCylinderIncl_contractAt A (TopCat.I.homeomorph.symm t)) c
    · change topologicalConeContractAt A (TopCat.I.homeomorph.symm t)
        (topologicalConePointIncl A z) = _
      exact ConcreteCategory.congr_hom
        (topologicalConePointIncl_contractAt A (TopCat.I.homeomorph.symm t)) z
  map_zero_left z := by
    change topologicalConeContractAt A 0 z = z
    rw [topologicalConeContractAt_zero]
    rfl
  map_one_left z := by
    change topologicalConeContractAt A 1 z =
      (toUnit (topologicalCone A) ≫ topologicalConePointIncl A) z
    rw [topologicalConeContractAt_one]

/-- Every topological cone is contractible. -/
instance (A : TopCat.{u}) : ContractibleSpace (topologicalCone A) :=
  (contractible_iff_id_nullhomotopic (topologicalCone A)).mpr
    ⟨topologicalConePointIncl A
        (SemiCartesianMonoidalCategory.isTerminalTensorUnit.from
          (TopCat.of PUnit.{u + 1}) PUnit.unit),
      ⟨topologicalConeContractHomotopy A⟩⟩

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

/-- The original space embeds in its mapping cone. -/
instance {A X : TopCat.{u}} (f : A ⟶ X) : Mono (topologicalMappingConeIncl f) := by
  unfold topologicalMappingConeIncl
  exact mono_pushout_inl_topCat f (topologicalConeBaseIncl A)

/-- The canonical map from the cone into `C_f`. -/
def topologicalMappingConeConeIncl {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalCone A ⟶ topologicalMappingCone f :=
  pushout.inr f (topologicalConeBaseIncl A)

/-- The quotient map from the original space, cone cylinder, and cone point onto a mapping cone. -/
def topologicalMappingConeTripleDesc {A X : TopCat.{u}} (f : A ⟶ X) :
    (X : Type u) ⊕ ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u})) →
      topologicalMappingCone f :=
  pushoutSumDesc f (topologicalConeBaseIncl A) ∘
    Sum.map id (topologicalConeSumDesc A)

theorem topologicalMappingConeTripleDesc_isQuotientMap {A X : TopCat.{u}} (f : A ⟶ X) :
    IsQuotientMap (topologicalMappingConeTripleDesc f) := by
  apply (pushoutSumDesc_isQuotientMap f (topologicalConeBaseIncl A)).comp
  apply IsQuotientMap.sumMap
  · exact IsQuotientMap.id
  · exact topologicalConeSumDesc_isQuotientMap A

/-- The height coordinate on a mapping cone, equal to zero on the original space and to cone
height on the cone summand. -/
def topologicalMappingConeHeight {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalMappingCone f ⟶ TopCat.I :=
  pushout.desc (TopCat.const 0) (topologicalConeHeight A) (by
    rw [topologicalConeBaseIncl_height]
    rfl)

@[reassoc (attr := simp)]
theorem topologicalMappingConeIncl_height {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalMappingConeIncl f ≫ topologicalMappingConeHeight f = TopCat.const 0 := by
  unfold topologicalMappingConeIncl topologicalMappingConeHeight
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalMappingConeConeIncl_height {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalMappingConeConeIncl f ≫ topologicalMappingConeHeight f =
      topologicalConeHeight A := by
  unfold topologicalMappingConeConeIncl topologicalMappingConeHeight
  exact pushout.inr_desc _ _ _

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
