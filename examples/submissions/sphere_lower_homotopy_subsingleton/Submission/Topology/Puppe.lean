/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.MappingConeCofibration
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

/-! ### Coexactness of the first mapping-cone pair -/

/-- A nullhomotopy of `f ≫ g` extends `g` across the mapping cone of `f`. -/
def topologicalMappingConeExtensionOfNullhomotopy
    {A X Y : TopCat.{u}} (f : A ⟶ X) (g : X ⟶ Y)
    (y : 𝟙_ TopCat.{u} ⟶ Y)
    (H : TopCat.Homotopy (f ≫ g) (toUnit A ≫ y)) :
    topologicalMappingCone f ⟶ Y :=
  pushout.desc g
    (topologicalConeExtensionOfNullhomotopy (f ≫ g) y H) (by
      rw [topologicalConeBaseIncl_extensionOfNullhomotopy])

@[reassoc (attr := simp)]
theorem topologicalMappingConeIncl_extensionOfNullhomotopy
    {A X Y : TopCat.{u}} (f : A ⟶ X) (g : X ⟶ Y)
    (y : 𝟙_ TopCat.{u} ⟶ Y)
    (H : TopCat.Homotopy (f ≫ g) (toUnit A ≫ y)) :
    topologicalMappingConeIncl f ≫
        topologicalMappingConeExtensionOfNullhomotopy f g y H = g :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalMappingConeConeIncl_extensionOfNullhomotopy
    {A X Y : TopCat.{u}} (f : A ⟶ X) (g : X ⟶ Y)
    (y : 𝟙_ TopCat.{u} ⟶ Y)
    (H : TopCat.Homotopy (f ≫ g) (toUnit A ≫ y)) :
    topologicalMappingConeConeIncl f ≫
        topologicalMappingConeExtensionOfNullhomotopy f g y H =
      topologicalConeExtensionOfNullhomotopy (f ≫ g) y H :=
  pushout.inr_desc _ _ _

/-- The image of the cone point under a proposed extension across a mapping cone. -/
def topologicalMappingConeExtensionPoint
    {A X Y : TopCat.{u}} (f : A ⟶ X)
    (h : topologicalMappingCone f ⟶ Y) : 𝟙_ TopCat.{u} ⟶ Y :=
  topologicalConePointIncl A ≫ topologicalMappingConeConeIncl f ≫ h

/-- Any extension of `g` across the mapping cone supplies a nullhomotopy of `f ≫ g`. -/
def topologicalMappingConeCompositeNullhomotopyOfExtension
    {A X Y : TopCat.{u}} (f : A ⟶ X) (g : X ⟶ Y)
    (h : topologicalMappingCone f ⟶ Y)
    (hh : topologicalMappingConeIncl f ≫ h = g) :
    TopCat.Homotopy (f ≫ g)
      (toUnit A ≫ topologicalMappingConeExtensionPoint f h) := by
  let k : topologicalCone A ⟶ Y := topologicalMappingConeConeIncl f ≫ h
  let Hcone : TopCat.Homotopy k
      ((toUnit (topologicalCone A) ≫ topologicalConePointIncl A) ≫ k) :=
    (TopCat.Homotopy.refl k).comp (topologicalConeContractHomotopy A)
  have Hbase := Hcone.comp
    (TopCat.Homotopy.refl (topologicalConeBaseIncl A))
  rw [← topologicalMappingCone_condition_assoc, hh] at Hbase
  have hunit : topologicalConeBaseIncl A ≫ toUnit (topologicalCone A) =
      toUnit A :=
    Subsingleton.elim _ _
  simpa only [k, topologicalMappingConeExtensionPoint, Category.id_comp,
    Category.comp_id, ← Category.assoc, hunit] using Hbase

/-- A map out of `X` extends across `C_f` exactly when its composite with `f` contracts to
some point. -/
theorem exists_topologicalMappingCone_extension_iff
    {A X Y : TopCat.{u}} (f : A ⟶ X) (g : X ⟶ Y) :
    (∃ h : topologicalMappingCone f ⟶ Y,
        topologicalMappingConeIncl f ≫ h = g) ↔
      ∃ y : 𝟙_ TopCat.{u} ⟶ Y,
        Nonempty (TopCat.Homotopy (f ≫ g) (toUnit A ≫ y)) := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨topologicalMappingConeExtensionPoint f h,
      ⟨topologicalMappingConeCompositeNullhomotopyOfExtension f g h hh⟩⟩
  · rintro ⟨y, ⟨H⟩⟩
    exact ⟨topologicalMappingConeExtensionOfNullhomotopy f g y H,
      topologicalMappingConeIncl_extensionOfNullhomotopy f g y H⟩

/-- Equivalently, extension across a mapping cone detects ordinary unbased nullhomotopy of the
composite. -/
theorem exists_topologicalMappingCone_extension_iff_nullhomotopic
    {A X Y : TopCat.{u}} (f : A ⟶ X) (g : X ⟶ Y) :
    (∃ h : topologicalMappingCone f ⟶ Y,
        topologicalMappingConeIncl f ≫ h = g) ↔
      (f ≫ g).hom.Nullhomotopic := by
  rw [exists_topologicalMappingCone_extension_iff]
  constructor
  · rintro ⟨y, ⟨H⟩⟩
    let z : Y := y
      (SemiCartesianMonoidalCategory.isTerminalTensorUnit.from
        (TopCat.of PUnit.{u + 1}) PUnit.unit)
    refine ⟨z, ⟨H.cast rfl ?_⟩⟩
    ext a
    change y (toUnit A a) = z
    let p : TopCat.of PUnit.{u + 1} ⟶ 𝟙_ TopCat.{u} :=
      TopCat.const (toUnit A a)
    have hp : p =
        SemiCartesianMonoidalCategory.isTerminalTensorUnit.from
          (TopCat.of PUnit.{u + 1}) :=
      SemiCartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
    exact congrArg y (ConcreteCategory.congr_hom hp PUnit.unit)
  · rintro ⟨z, ⟨H⟩⟩
    refine ⟨TopCat.const z, ⟨H.cast rfl ?_⟩⟩
    ext a
    rfl

/-! ### Strict coexactness at the mapping cone -/

/-- A map out of a mapping cone whose restriction to the target summand is constant descends
through the cofiber collapse. -/
def topologicalSuspensionDescOfMappingConeConstantRestriction
    {A X Y : TopCat.{u}} (f : A ⟶ X)
    (h : topologicalMappingCone f ⟶ Y) (y : 𝟙_ TopCat.{u} ⟶ Y)
    (hh : topologicalMappingConeIncl f ≫ h = toUnit X ≫ y) :
    topologicalSuspension A ⟶ Y :=
  pushout.desc y (topologicalMappingConeConeIncl f ≫ h) (by
    calc
      toUnit A ≫ y = (f ≫ toUnit X) ≫ y := by
        rw [toUnit_unique (toUnit A) (f ≫ toUnit X)]
      _ = f ≫ (toUnit X ≫ y) := Category.assoc _ _ _
      _ = f ≫ (topologicalMappingConeIncl f ≫ h) := by rw [hh]
      _ = (f ≫ topologicalMappingConeIncl f) ≫ h :=
        (Category.assoc _ _ _).symm
      _ = (topologicalConeBaseIncl A ≫
          topologicalMappingConeConeIncl f) ≫ h := by
        rw [topologicalMappingCone_condition]
      _ = topologicalConeBaseIncl A ≫
          (topologicalMappingConeConeIncl f ≫ h) := Category.assoc _ _ _)

@[reassoc (attr := simp)]
theorem topologicalSuspensionPointIncl_descOfMappingConeConstantRestriction
    {A X Y : TopCat.{u}} (f : A ⟶ X)
    (h : topologicalMappingCone f ⟶ Y) (y : 𝟙_ TopCat.{u} ⟶ Y)
    (hh : topologicalMappingConeIncl f ≫ h = toUnit X ≫ y) :
    topologicalSuspensionPointIncl A ≫
        topologicalSuspensionDescOfMappingConeConstantRestriction f h y hh = y :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalSuspensionConeIncl_descOfMappingConeConstantRestriction
    {A X Y : TopCat.{u}} (f : A ⟶ X)
    (h : topologicalMappingCone f ⟶ Y) (y : 𝟙_ TopCat.{u} ⟶ Y)
    (hh : topologicalMappingConeIncl f ≫ h = toUnit X ≫ y) :
    topologicalSuspensionConeIncl A ≫
        topologicalSuspensionDescOfMappingConeConstantRestriction f h y hh =
      topologicalMappingConeConeIncl f ≫ h :=
  pushout.inr_desc _ _ _

/-- The descended map recovers the original mapping-cone map after the cofiber collapse. -/
@[reassoc (attr := simp)]
theorem topologicalMappingConeCollapse_descOfMappingConeConstantRestriction
    {A X Y : TopCat.{u}} (f : A ⟶ X)
    (h : topologicalMappingCone f ⟶ Y) (y : 𝟙_ TopCat.{u} ⟶ Y)
    (hh : topologicalMappingConeIncl f ≫ h = toUnit X ≫ y) :
    topologicalMappingConeCollapse f ≫
        topologicalSuspensionDescOfMappingConeConstantRestriction f h y hh = h := by
  apply topologicalMappingCone_hom_ext f
  · rw [← Category.assoc, topologicalMappingConeIncl_collapse, Category.assoc,
      topologicalSuspensionPointIncl_descOfMappingConeConstantRestriction]
    exact hh.symm
  · rw [← Category.assoc, topologicalMappingConeConeIncl_collapse,
      topologicalSuspensionConeIncl_descOfMappingConeConstantRestriction]

/-- A map out of `C_f` factors through the cofiber collapse exactly when its restriction to
`X` is constant. -/
theorem exists_topologicalSuspension_factorization_iff_constant_restriction
    {A X Y : TopCat.{u}} (f : A ⟶ X)
    (h : topologicalMappingCone f ⟶ Y) :
    (∃ k : topologicalSuspension A ⟶ Y,
        topologicalMappingConeCollapse f ≫ k = h) ↔
      ∃ y : 𝟙_ TopCat.{u} ⟶ Y,
        topologicalMappingConeIncl f ≫ h = toUnit X ≫ y := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨topologicalSuspensionPointIncl A ≫ k, ?_⟩
    rw [← Category.assoc, topologicalMappingConeIncl_collapse, Category.assoc]
  · rintro ⟨y, hh⟩
    exact ⟨topologicalSuspensionDescOfMappingConeConstantRestriction f h y hh,
      topologicalMappingConeCollapse_descOfMappingConeConstantRestriction f h y hh⟩

/-! ### Homotopy coexactness at the mapping cone -/

/-- A map out of `C_f` factors through the cofiber collapse up to homotopy exactly when its
restriction to `X` is nullhomotopic.  This is the homotopy-invariant coexactness statement at the
mapping-cone term of the Puppe sequence. -/
theorem exists_topologicalSuspension_homotopy_factorization_iff_nullhomotopic_restriction
    {A X Y : TopCat.{u}} (f : A ⟶ X)
    (h : topologicalMappingCone f ⟶ Y) :
    (∃ k : topologicalSuspension A ⟶ Y,
        Nonempty (TopCat.Homotopy
          (topologicalMappingConeCollapse f ≫ k) h)) ↔
      (topologicalMappingConeIncl f ≫ h).hom.Nullhomotopic := by
  constructor
  · rintro ⟨k, ⟨Hfactor⟩⟩
    let y : 𝟙_ TopCat.{u} ⟶ Y := topologicalSuspensionPointIncl A ≫ k
    let Hpre := Hfactor.comp
      (TopCat.Homotopy.refl (topologicalMappingConeIncl f))
    have hend :
        topologicalMappingConeIncl f ≫
            (topologicalMappingConeCollapse f ≫ k) =
          toUnit X ≫ y := by
      calc
        _ = (topologicalMappingConeIncl f ≫
              topologicalMappingConeCollapse f) ≫ k :=
          (Category.assoc _ _ _).symm
        _ = (toUnit X ≫ topologicalSuspensionPointIncl A) ≫ k := by
          rw [topologicalMappingConeIncl_collapse]
        _ = toUnit X ≫ (topologicalSuspensionPointIncl A ≫ k) :=
          Category.assoc _ _ _
        _ = _ := rfl
    let Hrestriction : TopCat.Homotopy
        (topologicalMappingConeIncl f ≫ h) (toUnit X ≫ y) :=
      Hpre.symm.cast rfl (congrArg TopCat.Hom.hom hend)
    let z : Y := y
      (SemiCartesianMonoidalCategory.isTerminalTensorUnit.from
        (TopCat.of PUnit.{u + 1}) PUnit.unit)
    refine ⟨z, ⟨Hrestriction.cast rfl ?_⟩⟩
    ext x
    change y (toUnit X x) = z
    let p : TopCat.of PUnit.{u + 1} ⟶ 𝟙_ TopCat.{u} :=
      TopCat.const (toUnit X x)
    have hp : p =
        SemiCartesianMonoidalCategory.isTerminalTensorUnit.from
          (TopCat.of PUnit.{u + 1}) :=
      SemiCartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
    exact congrArg y (ConcreteCategory.congr_hom hp PUnit.unit)
  · rintro ⟨z, ⟨Hnull⟩⟩
    let Hwall : C(X × unitInterval, Y) :=
      Hnull.toContinuousMap.comp
        ⟨fun p ↦ (p.2, p.1), by fun_prop⟩
    have hcompat : h.hom ∘ (topologicalMappingConeIncl f).hom =
        Hwall ∘ (·, 0) := by
      funext x
      exact (Hnull.map_zero_left x).symm
    obtain ⟨G, hGzero, hGwall⟩ :=
      topologicalMappingConeIncl_hasHomotopyExtensionProperty f Y
        h.hom Hwall hcompat
    let h₁ : topologicalMappingCone f ⟶ Y :=
      TopCat.ofHom (G.comp ⟨fun c ↦ (c, 1), by fun_prop⟩)
    have hh₁ : topologicalMappingConeIncl f ≫ h₁ =
        toUnit X ≫ TopCat.const z := by
      apply TopCat.hom_ext
      ext x
      simp only [ConcreteCategory.comp_apply]
      change G (topologicalMappingConeIncl f x, 1) = z
      have hwall := congrFun hGwall (x, (1 : unitInterval))
      change Hnull (1, x) = G (topologicalMappingConeIncl f x, 1) at hwall
      exact hwall.symm.trans (Hnull.map_one_left x)
    let k : topologicalSuspension A ⟶ Y :=
      topologicalSuspensionDescOfMappingConeConstantRestriction
        f h₁ (TopCat.const z) hh₁
    have hk : topologicalMappingConeCollapse f ≫ k = h₁ :=
      topologicalMappingConeCollapse_descOfMappingConeConstantRestriction
        f h₁ (TopCat.const z) hh₁
    let HG : TopCat.Homotopy h h₁ := {
      toFun := fun p ↦ G (p.2, p.1)
      continuous_toFun := G.continuous.comp
        (continuous_snd.prodMk continuous_fst)
      map_zero_left := fun c ↦ (congrFun hGzero c).symm
      map_one_left := fun _ ↦ rfl }
    exact ⟨k, ⟨HG.symm.cast
      (congrArg TopCat.Hom.hom hk.symm) rfl⟩⟩

end Submission
