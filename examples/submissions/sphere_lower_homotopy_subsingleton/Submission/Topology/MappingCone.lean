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
* `Submission.topologicalMappingConeMap` and `Submission.topologicalMappingConeIso`;
* `Submission.topologicalConeExtensionOfNullhomotopy`;
* `Submission.topologicalMappingConeRetractOfNullhomotopy`;
* `Submission.topologicalMappingConeNullhomotopyOfRetract`.
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

/-! ### Functoriality of cones -/

/-- Apply a map to the space coordinate of a cone cylinder while preserving its height. -/
def topologicalConeCylinderMap {A B : TopCat.{u}} (a : A ⟶ B) :
    A ⊗ TopCat.I ⟶ B ⊗ TopCat.I :=
  lift (fst A TopCat.I ≫ a) (snd A TopCat.I)

@[simp]
theorem topologicalConeCylinderMap_apply {A B : TopCat.{u}} (a : A ⟶ B)
    (x : A) (t : TopCat.I) :
    topologicalConeCylinderMap a (x, t) = (a x, t) :=
  rfl

@[simp]
theorem topologicalConeCylinderMap_id (A : TopCat.{u}) :
    topologicalConeCylinderMap (𝟙 A) = 𝟙 (A ⊗ TopCat.I) := by
  apply TopCat.hom_ext
  ext p
  rcases p with ⟨x, t⟩
  rfl

theorem topologicalConeCylinderMap_comp {A B C : TopCat.{u}}
    (a : A ⟶ B) (b : B ⟶ C) :
    topologicalConeCylinderMap (a ≫ b) =
      topologicalConeCylinderMap a ≫ topologicalConeCylinderMap b := by
  apply TopCat.hom_ext
  ext p
  rcases p with ⟨x, t⟩
  rfl

@[reassoc]
theorem topologicalCone_ι₀_cylinderMap {A B : TopCat.{u}} (a : A ⟶ B) :
    TopCat.ι₀ ≫ topologicalConeCylinderMap a = a ≫ TopCat.ι₀ := by
  apply TopCat.hom_ext
  ext x
  rfl

@[reassoc]
theorem topologicalCone_ι₁_cylinderMap {A B : TopCat.{u}} (a : A ⟶ B) :
    TopCat.ι₁ ≫ topologicalConeCylinderMap a = a ≫ TopCat.ι₁ := by
  apply TopCat.hom_ext
  ext x
  rfl

/-- The map of topological cones induced by a continuous map. -/
def topologicalConeMap {A B : TopCat.{u}} (a : A ⟶ B) :
    topologicalCone A ⟶ topologicalCone B :=
  topologicalConeDesc A
    (topologicalConeCylinderMap a ≫ topologicalConeCylinderIncl B)
    (topologicalConePointIncl B) (by
      rw [← Category.assoc, topologicalCone_ι₁_cylinderMap]
      have hB : (TopCat.ι₁ : B ⟶ B ⊗ TopCat.I) ≫
          topologicalConeCylinderIncl B =
          toUnit B ≫ topologicalConePointIncl B :=
        pushout.condition
      rw [Category.assoc, hB]
      rfl)

@[reassoc (attr := simp)]
theorem topologicalConeCylinderIncl_map {A B : TopCat.{u}} (a : A ⟶ B) :
    topologicalConeCylinderIncl A ≫ topologicalConeMap a =
      topologicalConeCylinderMap a ≫ topologicalConeCylinderIncl B := by
  rw [topologicalConeMap, topologicalConeCylinderIncl_desc]

@[reassoc (attr := simp)]
theorem topologicalConePointIncl_map {A B : TopCat.{u}} (a : A ⟶ B) :
    topologicalConePointIncl A ≫ topologicalConeMap a =
      topologicalConePointIncl B := by
  rw [topologicalConeMap, topologicalConePointIncl_desc]

@[reassoc (attr := simp)]
theorem topologicalConeBaseIncl_map {A B : TopCat.{u}} (a : A ⟶ B) :
    topologicalConeBaseIncl A ≫ topologicalConeMap a =
      a ≫ topologicalConeBaseIncl B := by
  rw [topologicalConeBaseIncl, Category.assoc, topologicalConeCylinderIncl_map,
    ← Category.assoc, topologicalCone_ι₀_cylinderMap, Category.assoc]
  rfl

@[simp]
theorem topologicalConeMap_id (A : TopCat.{u}) :
    topologicalConeMap (𝟙 A) = 𝟙 (topologicalCone A) := by
  apply topologicalCone_hom_ext A
  · rw [topologicalConeCylinderIncl_map, topologicalConeCylinderMap_id,
      Category.id_comp, Category.comp_id]
  · rw [topologicalConePointIncl_map, Category.comp_id]

theorem topologicalConeMap_comp {A B C : TopCat.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    topologicalConeMap (a ≫ b) = topologicalConeMap a ≫ topologicalConeMap b := by
  apply topologicalCone_hom_ext A
  · calc
      _ = topologicalConeCylinderMap (a ≫ b) ≫
          topologicalConeCylinderIncl C :=
        topologicalConeCylinderIncl_map (a ≫ b)
      _ = (topologicalConeCylinderMap a ≫ topologicalConeCylinderMap b) ≫
          topologicalConeCylinderIncl C :=
        congrArg (fun k ↦ k ≫ topologicalConeCylinderIncl C)
          (topologicalConeCylinderMap_comp a b)
      _ = topologicalConeCylinderMap a ≫
          (topologicalConeCylinderMap b ≫ topologicalConeCylinderIncl C) :=
        Category.assoc _ _ _
      _ = topologicalConeCylinderMap a ≫
          (topologicalConeCylinderIncl B ≫ topologicalConeMap b) :=
        congrArg (fun k ↦ topologicalConeCylinderMap a ≫ k)
          (topologicalConeCylinderIncl_map b).symm
      _ = (topologicalConeCylinderMap a ≫ topologicalConeCylinderIncl B) ≫
          topologicalConeMap b :=
        (Category.assoc _ _ _).symm
      _ = (topologicalConeCylinderIncl A ≫ topologicalConeMap a) ≫
          topologicalConeMap b :=
        congrArg (fun k ↦ k ≫ topologicalConeMap b)
          (topologicalConeCylinderIncl_map a).symm
      _ = _ := Category.assoc _ _ _
  · calc
      _ = topologicalConePointIncl C := topologicalConePointIncl_map (a ≫ b)
      _ = topologicalConePointIncl B ≫ topologicalConeMap b :=
        (topologicalConePointIncl_map b).symm
      _ = (topologicalConePointIncl A ≫ topologicalConeMap a) ≫
          topologicalConeMap b :=
        congrArg (fun k ↦ k ≫ topologicalConeMap b)
          (topologicalConePointIncl_map a).symm
      _ = _ := Category.assoc _ _ _

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

/-- Maps out of a mapping cone are determined by their restrictions to the original space and
the cone summand. -/
theorem topologicalMappingCone_hom_ext {A X : TopCat.{u}} (f : A ⟶ X)
    {Y : TopCat.{u}} {p q : topologicalMappingCone f ⟶ Y}
    (hX : topologicalMappingConeIncl f ≫ p = topologicalMappingConeIncl f ≫ q)
    (hC : topologicalMappingConeConeIncl f ≫ p =
      topologicalMappingConeConeIncl f ≫ q) :
    p = q :=
  pushout.hom_ext hX hC

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

/-! ### Functoriality of mapping cones -/

/-- A commutative square of attaching maps induces a map of their topological mapping cones. -/
def topologicalMappingConeMap {A B X Y : TopCat.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (a : A ⟶ B) (x : X ⟶ Y)
    (h : f ≫ x = a ≫ g) :
    topologicalMappingCone f ⟶ topologicalMappingCone g :=
  pushout.desc
    (x ≫ topologicalMappingConeIncl g)
    (topologicalConeMap a ≫ topologicalMappingConeConeIncl g) (by
      rw [← Category.assoc, h, Category.assoc, topologicalMappingCone_condition]
      exact (topologicalConeBaseIncl_map_assoc a
        (topologicalMappingConeConeIncl g)).symm)

@[reassoc (attr := simp)]
theorem topologicalMappingConeIncl_map {A B X Y : TopCat.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (a : A ⟶ B) (x : X ⟶ Y)
    (h : f ≫ x = a ≫ g) :
    topologicalMappingConeIncl f ≫ topologicalMappingConeMap f g a x h =
      x ≫ topologicalMappingConeIncl g := by
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalMappingConeConeIncl_map {A B X Y : TopCat.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (a : A ⟶ B) (x : X ⟶ Y)
    (h : f ≫ x = a ≫ g) :
    topologicalMappingConeConeIncl f ≫ topologicalMappingConeMap f g a x h =
      topologicalConeMap a ≫ topologicalMappingConeConeIncl g := by
  exact pushout.inr_desc _ _ _

@[simp]
theorem topologicalMappingConeMap_id {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalMappingConeMap f f (𝟙 A) (𝟙 X) (by simp) =
      𝟙 (topologicalMappingCone f) := by
  apply topologicalMappingCone_hom_ext f
  · rw [topologicalMappingConeIncl_map, Category.id_comp, Category.comp_id]
  · rw [topologicalMappingConeConeIncl_map, topologicalConeMap_id,
      Category.id_comp, Category.comp_id]

theorem topologicalMappingConeMap_comp {A B C X Y Z : TopCat.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (k : C ⟶ Z)
    (a : A ⟶ B) (b : B ⟶ C) (x : X ⟶ Y) (y : Y ⟶ Z)
    (hfg : f ≫ x = a ≫ g) (hgk : g ≫ y = b ≫ k) :
    topologicalMappingConeMap f k (a ≫ b) (x ≫ y) (by
      rw [← Category.assoc, hfg, Category.assoc, hgk, ← Category.assoc]) =
      topologicalMappingConeMap f g a x hfg ≫
        topologicalMappingConeMap g k b y hgk := by
  apply topologicalMappingCone_hom_ext f
  · calc
      _ = (x ≫ y) ≫ topologicalMappingConeIncl k :=
        topologicalMappingConeIncl_map f k (a ≫ b) (x ≫ y) _
      _ = x ≫ (y ≫ topologicalMappingConeIncl k) := Category.assoc _ _ _
      _ = x ≫ (topologicalMappingConeIncl g ≫
          topologicalMappingConeMap g k b y hgk) :=
        congrArg (fun q ↦ x ≫ q)
          (topologicalMappingConeIncl_map g k b y hgk).symm
      _ = (x ≫ topologicalMappingConeIncl g) ≫
          topologicalMappingConeMap g k b y hgk :=
        (Category.assoc _ _ _).symm
      _ = (topologicalMappingConeIncl f ≫
          topologicalMappingConeMap f g a x hfg) ≫
          topologicalMappingConeMap g k b y hgk :=
        congrArg (fun q ↦ q ≫ topologicalMappingConeMap g k b y hgk)
          (topologicalMappingConeIncl_map f g a x hfg).symm
      _ = _ := Category.assoc _ _ _
  · calc
      _ = topologicalConeMap (a ≫ b) ≫ topologicalMappingConeConeIncl k :=
        topologicalMappingConeConeIncl_map f k (a ≫ b) (x ≫ y) _
      _ = (topologicalConeMap a ≫ topologicalConeMap b) ≫
          topologicalMappingConeConeIncl k :=
        congrArg (fun q ↦ q ≫ topologicalMappingConeConeIncl k)
          (topologicalConeMap_comp a b)
      _ = topologicalConeMap a ≫
          (topologicalConeMap b ≫ topologicalMappingConeConeIncl k) :=
        Category.assoc _ _ _
      _ = topologicalConeMap a ≫
          (topologicalMappingConeConeIncl g ≫
            topologicalMappingConeMap g k b y hgk) :=
        congrArg (fun q ↦ topologicalConeMap a ≫ q)
          (topologicalMappingConeConeIncl_map g k b y hgk).symm
      _ = (topologicalConeMap a ≫ topologicalMappingConeConeIncl g) ≫
          topologicalMappingConeMap g k b y hgk :=
        (Category.assoc _ _ _).symm
      _ = (topologicalMappingConeConeIncl f ≫
          topologicalMappingConeMap f g a x hfg) ≫
          topologicalMappingConeMap g k b y hgk :=
        congrArg (fun q ↦ q ≫ topologicalMappingConeMap g k b y hgk)
          (topologicalMappingConeConeIncl_map f g a x hfg).symm
      _ = _ := Category.assoc _ _ _

/-- The inverse sides of a commutative square of isomorphisms form the inverse commutative
square. -/
theorem topologicalMappingCone_inverse_square {A B X Y : TopCat.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (a : A ⟶ B) (x : X ⟶ Y)
    [IsIso a] [IsIso x] (h : f ≫ x = a ≫ g) :
    g ≫ inv x = inv a ≫ f := by
  apply (cancel_mono x).1
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    Category.assoc, h, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- A commutative square whose vertical maps are isomorphisms induces an isomorphism of
topological mapping cones. -/
def topologicalMappingConeIso {A B X Y : TopCat.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (a : A ⟶ B) (x : X ⟶ Y)
    [IsIso a] [IsIso x] (h : f ≫ x = a ≫ g) :
    topologicalMappingCone f ≅ topologicalMappingCone g where
  hom := topologicalMappingConeMap f g a x h
  inv := topologicalMappingConeMap g f (inv a) (inv x)
    (topologicalMappingCone_inverse_square f g a x h)
  hom_inv_id := by
    rw [← topologicalMappingConeMap_comp f g f a (inv a) x (inv x) h
      (topologicalMappingCone_inverse_square f g a x h)]
    simpa only [IsIso.hom_inv_id] using topologicalMappingConeMap_id f
  inv_hom_id := by
    rw [← topologicalMappingConeMap_comp g f g (inv a) a (inv x) x
      (topologicalMappingCone_inverse_square f g a x h) h]
    simpa only [IsIso.inv_hom_id] using topologicalMappingConeMap_id g

/-- Nullhomotopy is invariant under changing both sides of a commutative square by
isomorphisms. -/
theorem nullhomotopic_iff_of_iso_square {A B X Y : TopCat.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (a : A ≅ B) (x : X ≅ Y)
    (h : f ≫ x.hom = a.hom ≫ g) :
    f.hom.Nullhomotopic ↔ g.hom.Nullhomotopic := by
  constructor
  · intro hf
    have hfx : (f ≫ x.hom).hom.Nullhomotopic :=
      hf.comp_right x.hom.hom
    rw [h] at hfx
    have hpre := hfx.comp_left a.inv.hom
    have heq : a.inv ≫ (a.hom ≫ g) = g := by simp
    rw [← heq]
    exact hpre
  · intro hg
    have hag : (a.hom ≫ g).hom.Nullhomotopic :=
      hg.comp_left a.hom.hom
    rw [← h] at hag
    have hpost := hag.comp_right x.inv.hom
    have heq : (f ≫ x.hom) ≫ x.inv = f := by simp
    rw [← heq]
    exact hpost

/-! ### Suspension and the cofiber collapse -/

/-- The unreduced suspension of `A`, presented as the mapping cone of `A ⟶ *`. -/
def topologicalSuspension (A : TopCat.{u}) : TopCat.{u} :=
  topologicalMappingCone (toUnit A)

/-- One distinguished suspension point. -/
def topologicalSuspensionPointIncl (A : TopCat.{u}) :
    𝟙_ TopCat.{u} ⟶ topologicalSuspension A :=
  topologicalMappingConeIncl (toUnit A)

/-- Include the cone cylinder in the suspension. -/
def topologicalSuspensionConeIncl (A : TopCat.{u}) :
    topologicalCone A ⟶ topologicalSuspension A :=
  topologicalMappingConeConeIncl (toUnit A)

/-- Collapse the target summand of a mapping cone to obtain the suspension of its source. -/
def topologicalMappingConeCollapse {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalMappingCone f ⟶ topologicalSuspension A :=
  topologicalMappingConeMap f (toUnit A) (𝟙 A) (toUnit X) (by
    apply toUnit_unique)

@[reassoc (attr := simp)]
theorem topologicalMappingConeIncl_collapse {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalMappingConeIncl f ≫ topologicalMappingConeCollapse f =
      toUnit X ≫ topologicalSuspensionPointIncl A :=
  topologicalMappingConeIncl_map f (toUnit A) (𝟙 A) (toUnit X) _

@[reassoc (attr := simp)]
theorem topologicalMappingConeConeIncl_collapse {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalMappingConeConeIncl f ≫ topologicalMappingConeCollapse f =
      topologicalSuspensionConeIncl A := by
  unfold topologicalSuspensionConeIncl topologicalSuspension
  rw [topologicalMappingConeCollapse,
    topologicalMappingConeConeIncl_map, topologicalConeMap_id,
    Category.id_comp]

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

/-- The value at the cone point of a proposed retraction from a mapping cone. -/
def topologicalMappingConeRetractPoint {A X : TopCat.{u}} (f : A ⟶ X)
    (r : topologicalMappingCone f ⟶ X) : 𝟙_ TopCat.{u} ⟶ X :=
  topologicalConePointIncl A ≫ topologicalMappingConeConeIncl f ≫ r

/-- A retraction of the mapping-cone inclusion contracts the attaching map to the image of the
cone point.  Together with `topologicalMappingConeRetractOfNullhomotopy`, this characterizes
nullhomotopic attaching maps by retractions of their mapping-cone inclusions. -/
noncomputable def topologicalMappingConeNullhomotopyOfRetract
    {A X : TopCat.{u}} (f : A ⟶ X) (r : topologicalMappingCone f ⟶ X)
    (hr : topologicalMappingConeIncl f ≫ r = 𝟙 X) :
    TopCat.Homotopy f
      (toUnit A ≫ topologicalMappingConeRetractPoint f r) := by
  let g : topologicalCone A ⟶ X := topologicalMappingConeConeIncl f ≫ r
  let H : TopCat.Homotopy g
      ((toUnit (topologicalCone A) ≫ topologicalConePointIncl A) ≫ g) :=
    (TopCat.Homotopy.refl g).comp (topologicalConeContractHomotopy A)
  have Hbase := H.comp (TopCat.Homotopy.refl (topologicalConeBaseIncl A))
  rw [← topologicalMappingCone_condition_assoc, hr, Category.comp_id] at Hbase
  have hunit : topologicalConeBaseIncl A ≫ toUnit (topologicalCone A) = toUnit A :=
    Subsingleton.elim _ _
  simpa only [g, topologicalMappingConeRetractPoint, Category.id_comp,
    Category.comp_id, ← Category.assoc, hunit] using Hbase

/-- The inclusion of `X` into the mapping cone of `f` has a retraction exactly when `f` has a
nullhomotopy to some point of `X`. -/
theorem exists_topologicalMappingConeIncl_retraction_iff
    {A X : TopCat.{u}} (f : A ⟶ X) :
    (∃ r : topologicalMappingCone f ⟶ X,
        topologicalMappingConeIncl f ≫ r = 𝟙 X) ↔
      ∃ x : 𝟙_ TopCat.{u} ⟶ X,
        Nonempty (TopCat.Homotopy f (toUnit A ≫ x)) := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨topologicalMappingConeRetractPoint f r,
      ⟨topologicalMappingConeNullhomotopyOfRetract f r hr⟩⟩
  · rintro ⟨x, ⟨H⟩⟩
    exact ⟨topologicalMappingConeRetractOfNullhomotopy f x H,
      topologicalMappingConeIncl_retractOfNullhomotopy f x H⟩

/-- Equivalently, a mapping-cone inclusion retracts precisely when its attaching map is
nullhomotopic in the standard `ContinuousMap.Nullhomotopic` sense. -/
theorem exists_topologicalMappingConeIncl_retraction_iff_nullhomotopic
    {A X : TopCat.{u}} (f : A ⟶ X) :
    (∃ r : topologicalMappingCone f ⟶ X,
        topologicalMappingConeIncl f ≫ r = 𝟙 X) ↔
      f.hom.Nullhomotopic := by
  rw [exists_topologicalMappingConeIncl_retraction_iff]
  constructor
  · rintro ⟨x, ⟨H⟩⟩
    let z : X := x
      (SemiCartesianMonoidalCategory.isTerminalTensorUnit.from
        (TopCat.of PUnit.{u + 1}) PUnit.unit)
    refine ⟨z, ⟨H.cast rfl ?_⟩⟩
    ext a
    change x (toUnit A a) = z
    let p : TopCat.of PUnit.{u + 1} ⟶ 𝟙_ TopCat.{u} :=
      TopCat.const (toUnit A a)
    have hp : p =
        SemiCartesianMonoidalCategory.isTerminalTensorUnit.from
          (TopCat.of PUnit.{u + 1}) :=
      SemiCartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
    exact congrArg x (ConcreteCategory.congr_hom hp PUnit.unit)
  · rintro ⟨x, ⟨H⟩⟩
    refine ⟨TopCat.const x, ⟨H.cast rfl ?_⟩⟩
    ext a
    rfl

/-- If the target is path connected, the endpoint in the mapping-cone retraction criterion can
be replaced by any prescribed constant map. -/
theorem exists_topologicalMappingConeIncl_retraction_iff_homotopy_const
    {A X : TopCat.{u}} [PathConnectedSpace X] (f : A ⟶ X) (x : X) :
    (∃ r : topologicalMappingCone f ⟶ X,
        topologicalMappingConeIncl f ≫ r = 𝟙 X) ↔
      Nonempty (TopCat.Homotopy f (TopCat.const x)) := by
  rw [exists_topologicalMappingConeIncl_retraction_iff_nullhomotopic]
  constructor
  · rintro ⟨y, ⟨H⟩⟩
    exact ⟨H.trans (PathConnectedSpace.somePath y x).toHomotopyConst⟩
  · rintro ⟨H⟩
    exact ⟨x, ⟨H⟩⟩

/-- A homotopy retraction of the mapping-cone inclusion also contracts the attaching map. -/
noncomputable def topologicalMappingConeNullhomotopyOfHomotopyRetract
    {A X : TopCat.{u}} (f : A ⟶ X) (r : topologicalMappingCone f ⟶ X)
    (Hr : TopCat.Homotopy (topologicalMappingConeIncl f ≫ r) (𝟙 X)) :
    TopCat.Homotopy f
      (toUnit A ≫ topologicalMappingConeRetractPoint f r) := by
  let g : topologicalCone A ⟶ X := topologicalMappingConeConeIncl f ≫ r
  let Hcone : TopCat.Homotopy g
      ((toUnit (topologicalCone A) ≫ topologicalConePointIncl A) ≫ g) :=
    (TopCat.Homotopy.refl g).comp (topologicalConeContractHomotopy A)
  have Hbase := Hcone.comp (TopCat.Homotopy.refl (topologicalConeBaseIncl A))
  rw [← topologicalMappingCone_condition_assoc] at Hbase
  have hunit : topologicalConeBaseIncl A ≫ toUnit (topologicalCone A) = toUnit A :=
    Subsingleton.elim _ _
  have Hbase' : TopCat.Homotopy
      (f ≫ (topologicalMappingConeIncl f ≫ r))
      (toUnit A ≫ topologicalMappingConeRetractPoint f r) := by
    simpa only [g, topologicalMappingConeRetractPoint, Category.id_comp,
      Category.comp_id, ← Category.assoc, hunit] using Hbase
  have Hret : TopCat.Homotopy
      (f ≫ (topologicalMappingConeIncl f ≫ r)) f := by
    simpa only [Category.comp_id] using
      Hr.comp (TopCat.Homotopy.refl f)
  exact Hret.symm.trans Hbase'

/-- The mapping-cone inclusion has a homotopy retraction exactly when its attaching map is
nullhomotopic. -/
theorem exists_topologicalMappingConeIncl_homotopy_retraction_iff_nullhomotopic
    {A X : TopCat.{u}} (f : A ⟶ X) :
    (∃ r : topologicalMappingCone f ⟶ X,
        Nonempty
          (TopCat.Homotopy (topologicalMappingConeIncl f ≫ r) (𝟙 X))) ↔
      f.hom.Nullhomotopic := by
  constructor
  · rintro ⟨r, ⟨Hr⟩⟩
    rw [← exists_topologicalMappingConeIncl_retraction_iff_nullhomotopic]
    let x := topologicalMappingConeRetractPoint f r
    let H := topologicalMappingConeNullhomotopyOfHomotopyRetract f r Hr
    exact ⟨topologicalMappingConeRetractOfNullhomotopy f x H,
      topologicalMappingConeIncl_retractOfNullhomotopy f x H⟩
  · intro hf
    obtain ⟨r, hr⟩ :=
      (exists_topologicalMappingConeIncl_retraction_iff_nullhomotopic f).2 hf
    exact ⟨r, ⟨(TopCat.Homotopy.refl
      (topologicalMappingConeIncl f ≫ r)).cast rfl
        (congrArg TopCat.Hom.hom hr)⟩⟩

end Submission
