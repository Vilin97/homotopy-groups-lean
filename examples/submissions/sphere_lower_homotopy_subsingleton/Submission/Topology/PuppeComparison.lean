/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.Puppe

/-!
# The next comparison in the topological Puppe sequence

For `f : A ⟶ X`, form the mapping cone of the cofiber collapse
`C_f ⟶ ΣA`.  Its target inclusion is followed by `Σf`, and the canonical
nullhomotopy of that composite therefore extends `Σf` across the second mapping cone.

In the other direction, the suspension of `X` maps into the second mapping cone by sending its
cone through `CX ⟶ C(C_f)` and its distinguished point through `ΣA`.  These are the two
point-set comparison maps underlying the next stage of the Puppe sequence.
-/

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory
  CartesianMonoidalCategory
open scoped Topology TopCat

noncomputable section

namespace Submission

universe u

variable {A X : TopCat.{u}}

/-- A direct radial form of the canonical nullhomotopy of
`C_f ⟶ ΣA ⟶ ΣX`.  Its value on the original-space summand traces the ordinary cone
cylinder in `CX`, which makes the second Puppe comparison transparent. -/
def topologicalMappingConeCollapseSuspensionRadialNullhomotopy (f : A ⟶ X) :
    TopCat.Homotopy
      (topologicalMappingConeCollapse f ≫ topologicalSuspensionMap A f)
      (toUnit (topologicalMappingCone f) ≫
        topologicalConePointIncl X ≫ topologicalSuspensionConeIncl X) where
  toFun p := topologicalSuspensionConeIncl X
    (topologicalConeContractHomotopy X
      (p.1, topologicalMappingConeToCone f p.2))
  continuous_toFun := (topologicalSuspensionConeIncl X).hom.continuous.comp
    ((topologicalConeContractHomotopy X).continuous.comp
      (continuous_fst.prodMk
        ((topologicalMappingConeToCone f).hom.continuous.comp continuous_snd)))
  map_zero_left c := by
    change topologicalSuspensionConeIncl X
        (topologicalConeContractHomotopy X
          (0, topologicalMappingConeToCone f c)) =
      (topologicalMappingConeCollapse f ≫
        topologicalSuspensionMap A f) c
    calc
      _ = topologicalSuspensionConeIncl X
          (topologicalMappingConeToCone f c) := congrArg
        (topologicalSuspensionConeIncl X)
        ((topologicalConeContractHomotopy X).map_zero_left
          (topologicalMappingConeToCone f c))
      _ = _ := ConcreteCategory.congr_hom
        (topologicalMappingConeCollapse_suspensionMap f).symm c
  map_one_left c := by
    change topologicalSuspensionConeIncl X
        (topologicalConeContractHomotopy X
          (1, topologicalMappingConeToCone f c)) =
      (toUnit (topologicalMappingCone f) ≫
        topologicalConePointIncl X ≫ topologicalSuspensionConeIncl X) c
    calc
      _ = topologicalSuspensionConeIncl X
          ((toUnit (topologicalCone X) ≫ topologicalConePointIncl X)
            (topologicalMappingConeToCone f c)) := congrArg
        (topologicalSuspensionConeIncl X)
        ((topologicalConeContractHomotopy X).map_one_left
          (topologicalMappingConeToCone f c))
      _ = _ := by rfl

/-- The canonical comparison from the mapping cone of `C_f ⟶ ΣA` to `ΣX`. -/
def topologicalSecondMappingConeToSuspension (f : A ⟶ X) :
    topologicalMappingCone (topologicalMappingConeCollapse f) ⟶
      topologicalSuspension X :=
    topologicalMappingConeExtensionOfNullhomotopy
    (topologicalMappingConeCollapse f) (topologicalSuspensionMap A f)
    (topologicalConePointIncl X ≫ topologicalSuspensionConeIncl X)
    (topologicalMappingConeCollapseSuspensionRadialNullhomotopy f)

@[reassoc (attr := simp)]
theorem topologicalSecondMappingConeIncl_toSuspension (f : A ⟶ X) :
    topologicalMappingConeIncl (topologicalMappingConeCollapse f) ≫
        topologicalSecondMappingConeToSuspension f =
      topologicalSuspensionMap A f :=
  topologicalMappingConeIncl_extensionOfNullhomotopy _ _ _ _

@[reassoc (attr := simp)]
theorem topologicalSecondMappingConeConeIncl_toSuspension (f : A ⟶ X) :
    topologicalMappingConeConeIncl (topologicalMappingConeCollapse f) ≫
        topologicalSecondMappingConeToSuspension f =
      topologicalConeExtensionOfNullhomotopy
        (topologicalMappingConeCollapse f ≫ topologicalSuspensionMap A f)
        (topologicalConePointIncl X ≫ topologicalSuspensionConeIncl X)
        (topologicalMappingConeCollapseSuspensionRadialNullhomotopy f) :=
  topologicalMappingConeConeIncl_extensionOfNullhomotopy _ _ _ _

@[reassoc (attr := simp)]
theorem topologicalConeCylinderIncl_extensionOfNullhomotopy_h
    {B Y : TopCat.{u}} (g : B ⟶ Y) (y : 𝟙_ TopCat.{u} ⟶ Y)
    (H : TopCat.Homotopy g (toUnit B ≫ y)) :
    topologicalConeCylinderIncl B ≫
        topologicalConeExtensionOfNullhomotopy g y H = H.h := by
  rw [topologicalConeExtensionOfNullhomotopy,
    topologicalConeCylinderIncl_desc]

@[reassoc (attr := simp)]
theorem topologicalConePointIncl_extensionOfNullhomotopy
    {B Y : TopCat.{u}} (g : B ⟶ Y) (y : 𝟙_ TopCat.{u} ⟶ Y)
    (H : TopCat.Homotopy g (toUnit B ≫ y)) :
    topologicalConePointIncl B ≫
        topologicalConeExtensionOfNullhomotopy g y H = y := by
  rw [topologicalConeExtensionOfNullhomotopy,
    topologicalConePointIncl_desc]

/-- Along the original-space summand, the canonical nullhomotopy traces the ordinary cone
cylinder in `CX`. -/
theorem topologicalConeCylinderMap_incl_collapseSuspensionNullhomotopy_h
    (f : A ⟶ X) :
    topologicalConeCylinderMap (topologicalMappingConeIncl f) ≫
        (topologicalMappingConeCollapseSuspensionRadialNullhomotopy f).h =
      topologicalConeCylinderIncl X ≫ topologicalSuspensionConeIncl X := by
  apply TopCat.hom_ext
  ext p
  rcases p with ⟨x, t⟩
  simp only [ConcreteCategory.comp_apply, topologicalConeCylinderMap_apply,
    TopCat.Homotopy.h_hom_apply]
  change topologicalSuspensionConeIncl X
      (topologicalConeContractAt X
        (TopCat.I.homeomorph.symm (TopCat.I.homeomorph t))
        (topologicalMappingConeToCone f (topologicalMappingConeIncl f x))) =
    topologicalSuspensionConeIncl X (topologicalConeCylinderIncl X (x, t))
  rw [TopCat.I.homeomorph.symm_apply_apply]
  have hbase := ConcreteCategory.congr_hom
    (topologicalMappingConeIncl_toCone f) x
  change topologicalMappingConeToCone f (topologicalMappingConeIncl f x) =
    topologicalConeBaseIncl X x at hbase
  rw [hbase]
  have hbaseApply : topologicalConeBaseIncl X x =
      topologicalConeCylinderIncl X (x, (0 : TopCat.I.{u})) := by
    rfl
  rw [hbaseApply]
  have hcontract := ConcreteCategory.congr_hom
    (topologicalConeCylinderIncl_contractAt X t) (x, (0 : TopCat.I.{u}))
  change topologicalConeContractAt X t
      (topologicalConeCylinderIncl X (x, 0)) =
    topologicalConeCylinderIncl X (x, TopCat.I.max (0, t)) at hcontract
  rw [TopCat.I.max_zero_left] at hcontract
  exact congrArg (topologicalSuspensionConeIncl X) hcontract

/-- The canonical map from `ΣX` back to the mapping cone of `C_f ⟶ ΣA`. -/
def topologicalSuspensionToSecondMappingCone (f : A ⟶ X) :
    topologicalSuspension X ⟶
      topologicalMappingCone (topologicalMappingConeCollapse f) :=
  pushout.desc
    (topologicalSuspensionPointIncl A ≫
      topologicalMappingConeIncl (topologicalMappingConeCollapse f))
    (topologicalConeMap (topologicalMappingConeIncl f) ≫
      topologicalMappingConeConeIncl (topologicalMappingConeCollapse f)) (by
        calc
          toUnit X ≫ (topologicalSuspensionPointIncl A ≫
              topologicalMappingConeIncl (topologicalMappingConeCollapse f)) =
            (toUnit X ≫ topologicalSuspensionPointIncl A) ≫
              topologicalMappingConeIncl (topologicalMappingConeCollapse f) :=
            (Category.assoc _ _ _).symm
          _ = (topologicalMappingConeIncl f ≫
                topologicalMappingConeCollapse f) ≫
              topologicalMappingConeIncl (topologicalMappingConeCollapse f) := by
            rw [topologicalMappingConeIncl_collapse]
          _ = topologicalMappingConeIncl f ≫
              (topologicalMappingConeCollapse f ≫
                topologicalMappingConeIncl (topologicalMappingConeCollapse f)) :=
            Category.assoc _ _ _
          _ = topologicalMappingConeIncl f ≫
              (topologicalConeBaseIncl (topologicalMappingCone f) ≫
                topologicalMappingConeConeIncl
                  (topologicalMappingConeCollapse f)) := by
            rw [topologicalMappingCone_condition]
          _ = (topologicalMappingConeIncl f ≫
                topologicalConeBaseIncl (topologicalMappingCone f)) ≫
              topologicalMappingConeConeIncl
                (topologicalMappingConeCollapse f) :=
            (Category.assoc _ _ _).symm
          _ = (topologicalConeBaseIncl X ≫
                topologicalConeMap (topologicalMappingConeIncl f)) ≫
              topologicalMappingConeConeIncl
                (topologicalMappingConeCollapse f) := by
            rw [topologicalConeBaseIncl_map]
          _ = topologicalConeBaseIncl X ≫
              (topologicalConeMap (topologicalMappingConeIncl f) ≫
                topologicalMappingConeConeIncl
                  (topologicalMappingConeCollapse f)) :=
            Category.assoc _ _ _)

@[reassoc (attr := simp)]
theorem topologicalSuspensionPointIncl_toSecondMappingCone (f : A ⟶ X) :
    topologicalSuspensionPointIncl X ≫
        topologicalSuspensionToSecondMappingCone f =
      topologicalSuspensionPointIncl A ≫
        topologicalMappingConeIncl (topologicalMappingConeCollapse f) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalSuspensionConeIncl_toSecondMappingCone (f : A ⟶ X) :
    topologicalSuspensionConeIncl X ≫
        topologicalSuspensionToSecondMappingCone f =
      topologicalConeMap (topologicalMappingConeIncl f) ≫
        topologicalMappingConeConeIncl (topologicalMappingConeCollapse f) :=
  pushout.inr_desc _ _ _

/-- The comparison composite is already the identity on the distinguished suspension point. -/
theorem topologicalSuspensionPointIncl_toSecondMappingCone_toSuspension
    (f : A ⟶ X) :
    topologicalSuspensionPointIncl X ≫
        topologicalSuspensionToSecondMappingCone f ≫
          topologicalSecondMappingConeToSuspension f =
      topologicalSuspensionPointIncl X := by
  rw [← Category.assoc, topologicalSuspensionPointIncl_toSecondMappingCone,
    Category.assoc, topologicalSecondMappingConeIncl_toSuspension,
    topologicalSuspensionPointIncl_map]

/-- The comparison composite is the identity on the cone summand of the suspension. -/
theorem topologicalSuspensionConeIncl_toSecondMappingCone_toSuspension
    (f : A ⟶ X) :
    topologicalSuspensionConeIncl X ≫
        topologicalSuspensionToSecondMappingCone f ≫
          topologicalSecondMappingConeToSuspension f =
      topologicalSuspensionConeIncl X := by
  rw [← Category.assoc, topologicalSuspensionConeIncl_toSecondMappingCone,
    Category.assoc, topologicalSecondMappingConeConeIncl_toSuspension]
  apply topologicalCone_hom_ext X
  · rw [← Category.assoc, topologicalConeCylinderIncl_map, Category.assoc,
      topologicalConeCylinderIncl_extensionOfNullhomotopy_h]
    exact
      topologicalConeCylinderMap_incl_collapseSuspensionNullhomotopy_h f
  · calc
      _ = (topologicalConePointIncl X ≫
            topologicalConeMap (topologicalMappingConeIncl f)) ≫
          topologicalConeExtensionOfNullhomotopy
            (topologicalMappingConeCollapse f ≫ topologicalSuspensionMap A f)
            (topologicalConePointIncl X ≫ topologicalSuspensionConeIncl X)
            (topologicalMappingConeCollapseSuspensionRadialNullhomotopy f) :=
        (Category.assoc _ _ _).symm
      _ = topologicalConePointIncl (topologicalMappingCone f) ≫
          topologicalConeExtensionOfNullhomotopy
            (topologicalMappingConeCollapse f ≫ topologicalSuspensionMap A f)
            (topologicalConePointIncl X ≫ topologicalSuspensionConeIncl X)
            (topologicalMappingConeCollapseSuspensionRadialNullhomotopy f) := by
        rw [topologicalConePointIncl_map]
      _ = _ := topologicalConePointIncl_extensionOfNullhomotopy _ _ _

/-- The map `ΣX ⟶ C_(C_f ⟶ ΣA)` is an exact right inverse of the canonical comparison back to
`ΣX`. -/
theorem topologicalSuspensionToSecondMappingCone_toSuspension (f : A ⟶ X) :
    topologicalSuspensionToSecondMappingCone f ≫
        topologicalSecondMappingConeToSuspension f =
      𝟙 (topologicalSuspension X) := by
  apply topologicalMappingCone_hom_ext (toUnit X)
  · simpa only [topologicalSuspensionPointIncl, topologicalSuspension,
      Category.comp_id] using
      topologicalSuspensionPointIncl_toSecondMappingCone_toSuspension f
  · simpa only [topologicalSuspensionConeIncl, topologicalSuspension,
      Category.comp_id] using
      topologicalSuspensionConeIncl_toSecondMappingCone_toSuspension f

/-- The cofiber collapse has a homotopy retraction precisely when the target summand is itself
nullhomotopic inside the mapping cone.  This is the identity-map specialization of homotopy
coexactness at `C_f`. -/
theorem exists_topologicalMappingConeCollapse_homotopy_retraction_iff_incl_nullhomotopic
    (f : A ⟶ X) :
    (∃ r : topologicalSuspension A ⟶ topologicalMappingCone f,
        Nonempty (TopCat.Homotopy
          (topologicalMappingConeCollapse f ≫ r)
          (𝟙 (topologicalMappingCone f)))) ↔
      (topologicalMappingConeIncl f).hom.Nullhomotopic := by
  simpa only [Category.comp_id] using
    (exists_topologicalSuspension_homotopy_factorization_iff_nullhomotopic_restriction
      f (𝟙 (topologicalMappingCone f)))

end Submission
