/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Model.Suspension
import Submission.Topology.MappingCone

/-!
# Comparing two models of the unreduced suspension

The pushout suspension defined as the mapping cone of a map to a point is naturally
homeomorphic to the explicit quotient suspension `Susp`. The comparison uses the interval
coordinate homeomorphism built into `TopCat.I`, records exact formulas at both poles and on
the cone cylinder, and proves naturality with respect to maps of spaces.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology TopCat unitInterval

noncomputable section

namespace Submission

universe u

variable (A : TopCat.{u}) [Nonempty A]

noncomputable def topologicalConeCylinderToSusp :
    A ⊗ TopCat.I ⟶ TopCat.of (Susp A) :=
  TopCat.ofHom ⟨fun p ↦ Susp.mk (TopCat.I.homeomorph p.2, p.1), by
    fun_prop⟩

noncomputable def topologicalConeToSusp :
    topologicalCone A ⟶ TopCat.of (Susp A) :=
  topologicalConeDesc A (topologicalConeCylinderToSusp A)
    (TopCat.const (Susp.north A)) (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro a
      change Susp.mk (TopCat.I.homeomorph (1 : TopCat.I.{u}), a) = Susp.north A
      rw [TopCat.I.homeomorph_one, Susp.mk_one])

@[simp]
theorem topologicalConeToSusp_cylinder (a : A) (t : TopCat.I.{u}) :
    topologicalConeToSusp A (topologicalConeCylinderIncl A (a, t)) =
      Susp.mk (TopCat.I.homeomorph t, a) := by
  exact ConcreteCategory.congr_hom
    (topologicalConeCylinderIncl_desc A
      (topologicalConeCylinderToSusp A)
      (TopCat.const (Susp.north A)) _) (a, t)

@[simp]
theorem topologicalConeToSusp_point (p : PUnit) :
    topologicalConeToSusp A (topologicalConePointIncl A p) =
      Susp.north A := by
  exact ConcreteCategory.congr_hom
    (topologicalConePointIncl_desc A
      (topologicalConeCylinderToSusp A)
      (TopCat.const (Susp.north A)) _) p

noncomputable def topologicalSuspensionToSusp :
    topologicalSuspension A ⟶ TopCat.of (Susp A) :=
  pushout.desc (TopCat.const (Susp.south A))
    (topologicalConeToSusp A) (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro a
      change Susp.south A =
        topologicalConeToSusp A (topologicalConeBaseIncl A a)
      rw [show topologicalConeToSusp A (topologicalConeBaseIncl A a) =
          Susp.mk (TopCat.I.homeomorph (0 : TopCat.I.{u}), a) by
        rw [topologicalConeBaseIncl]
        exact topologicalConeToSusp_cylinder A a 0]
      rw [TopCat.I.homeomorph_zero, Susp.mk_zero])

@[reassoc (attr := simp)]
theorem topologicalSuspensionPointIncl_toSusp :
    topologicalSuspensionPointIncl A ≫ topologicalSuspensionToSusp A =
      TopCat.const (Susp.south A) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalSuspensionConeIncl_toSusp :
    topologicalSuspensionConeIncl A ≫ topologicalSuspensionToSusp A =
      topologicalConeToSusp A :=
  pushout.inr_desc _ _ _

@[simp]
theorem topologicalSuspensionToSusp_point (p : PUnit) :
    topologicalSuspensionToSusp A
      (topologicalSuspensionPointIncl A p) = Susp.south A := by
  exact ConcreteCategory.congr_hom
    (topologicalSuspensionPointIncl_toSusp A) p

@[simp]
theorem topologicalSuspensionToSusp_cone
    (c : topologicalCone A) :
    topologicalSuspensionToSusp A
        (topologicalSuspensionConeIncl A c) = topologicalConeToSusp A c := by
  exact ConcreteCategory.congr_hom
    (topologicalSuspensionConeIncl_toSusp A) c

noncomputable def suspCylinderToTopologicalSuspension :
    C(unitInterval × A, topologicalSuspension A) :=
  ⟨fun p ↦ topologicalSuspensionConeIncl A
      (topologicalConeCylinderIncl A
        (p.2, TopCat.I.homeomorph.symm p.1)), by
    fun_prop⟩

omit [Nonempty A] in
theorem suspCylinderToTopologicalSuspension_zero (a b : A) :
    suspCylinderToTopologicalSuspension A (0, a) =
      suspCylinderToTopologicalSuspension A (0, b) := by
  have hcondition := topologicalMappingCone_condition (toUnit A)
  have ha := ConcreteCategory.congr_hom hcondition a
  have hb := ConcreteCategory.congr_hom hcondition b
  change topologicalSuspensionPointIncl A (toUnit A a) =
    topologicalSuspensionConeIncl A (topologicalConeBaseIncl A a) at ha
  change topologicalSuspensionPointIncl A (toUnit A b) =
    topologicalSuspensionConeIncl A (topologicalConeBaseIncl A b) at hb
  have hu : toUnit A a = toUnit A b := by
    rfl
  have hbase : topologicalSuspensionConeIncl A (topologicalConeBaseIncl A a) =
      topologicalSuspensionConeIncl A (topologicalConeBaseIncl A b) :=
    ha.symm.trans <| (congrArg (topologicalSuspensionPointIncl A)
      hu).trans hb
  have hzero : TopCat.I.homeomorph.symm (0 : unitInterval) =
      (0 : TopCat.I.{u}) := by
    apply TopCat.I.homeomorph.injective
    simp
  change topologicalSuspensionConeIncl A
      (topologicalConeCylinderIncl A
        (a, TopCat.I.homeomorph.symm (0 : unitInterval))) =
    topologicalSuspensionConeIncl A
      (topologicalConeCylinderIncl A
        (b, TopCat.I.homeomorph.symm (0 : unitInterval)))
  rw [hzero]
  simpa [topologicalConeBaseIncl] using hbase

omit [Nonempty A] in
theorem suspCylinderToTopologicalSuspension_one (a b : A) :
    suspCylinderToTopologicalSuspension A (1, a) =
      suspCylinderToTopologicalSuspension A (1, b) := by
  have htop :
      (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) ≫ topologicalConeCylinderIncl A =
        toUnit A ≫ topologicalConePointIncl A :=
    pushout.condition
  have ha := ConcreteCategory.congr_hom htop a
  have hb := ConcreteCategory.congr_hom htop b
  change topologicalConeCylinderIncl A (a, (1 : TopCat.I.{u})) =
    topologicalConePointIncl A PUnit.unit at ha
  change topologicalConeCylinderIncl A (b, (1 : TopCat.I.{u})) =
    topologicalConePointIncl A PUnit.unit at hb
  have hone : TopCat.I.homeomorph.symm (1 : unitInterval) =
      (1 : TopCat.I.{u}) := by
    apply TopCat.I.homeomorph.injective
    simp
  change topologicalSuspensionConeIncl A
      (topologicalConeCylinderIncl A
        (a, TopCat.I.homeomorph.symm (1 : unitInterval))) =
    topologicalSuspensionConeIncl A
      (topologicalConeCylinderIncl A
        (b, TopCat.I.homeomorph.symm (1 : unitInterval)))
  rw [hone]
  exact congrArg (topologicalSuspensionConeIncl A) (ha.trans hb.symm)

noncomputable def suspToTopologicalSuspension :
    TopCat.of (Susp A) ⟶ topologicalSuspension A :=
  TopCat.ofHom (Susp.lift (suspCylinderToTopologicalSuspension A)
    (suspCylinderToTopologicalSuspension_zero A)
    (suspCylinderToTopologicalSuspension_one A))

omit [Nonempty A] in
@[simp]
theorem suspToTopologicalSuspension_mk (t : unitInterval) (a : A) :
    suspToTopologicalSuspension A (Susp.mk (t, a)) =
      topologicalSuspensionConeIncl A
        (topologicalConeCylinderIncl A
          (a, TopCat.I.homeomorph.symm t)) :=
  rfl

theorem suspToTopologicalSuspension_comp_toSusp :
    suspToTopologicalSuspension A ≫ topologicalSuspensionToSusp A =
      𝟙 (TopCat.of (Susp A)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  induction q using Susp.ind with
  | h p =>
      rcases p with ⟨t, a⟩
      rw [ConcreteCategory.comp_apply, suspToTopologicalSuspension_mk,
        topologicalSuspensionToSusp_cone,
        topologicalConeToSusp_cylinder, ConcreteCategory.id_apply]
      change Susp.mk (TopCat.I.homeomorph.{u}
        (TopCat.I.homeomorph.{u}.symm t), a) = Susp.mk (t, a)
      rw [TopCat.I.homeomorph.{u}.apply_symm_apply]

@[simp]
theorem suspToTopologicalSuspension_south :
    suspToTopologicalSuspension A (Susp.south A) =
      topologicalSuspensionPointIncl A PUnit.unit := by
  rw [Susp.south, suspToTopologicalSuspension_mk]
  have hzero : TopCat.I.homeomorph.symm (0 : unitInterval) =
      (0 : TopCat.I.{u}) := by
    apply TopCat.I.homeomorph.injective
    simp
  rw [hzero]
  have hcondition := topologicalMappingCone_condition (toUnit A)
  have ha := ConcreteCategory.congr_hom hcondition (Classical.arbitrary A)
  change topologicalSuspensionPointIncl A PUnit.unit =
    topologicalSuspensionConeIncl A
      (topologicalConeBaseIncl A (Classical.arbitrary A)) at ha
  simpa [topologicalConeBaseIncl] using ha.symm

@[simp]
theorem suspToTopologicalSuspension_north :
    suspToTopologicalSuspension A (Susp.north A) =
      topologicalSuspensionConeIncl A
        (topologicalConePointIncl A PUnit.unit) := by
  rw [Susp.north, suspToTopologicalSuspension_mk]
  have hone : TopCat.I.homeomorph.symm (1 : unitInterval) =
      (1 : TopCat.I.{u}) := by
    apply TopCat.I.homeomorph.injective
    simp
  rw [hone]
  have htop :
      (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) ≫ topologicalConeCylinderIncl A =
        toUnit A ≫ topologicalConePointIncl A :=
    pushout.condition
  have ha := ConcreteCategory.congr_hom htop (Classical.arbitrary A)
  change topologicalConeCylinderIncl A
      (Classical.arbitrary A, (1 : TopCat.I.{u})) =
    topologicalConePointIncl A PUnit.unit at ha
  exact congrArg (topologicalSuspensionConeIncl A) ha

theorem topologicalSuspensionToSusp_comp_suspTo :
    topologicalSuspensionToSusp A ≫ suspToTopologicalSuspension A =
      𝟙 (topologicalSuspension A) := by
  apply topologicalMappingCone_hom_ext (toUnit A)
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    cases p
    change suspToTopologicalSuspension A
        (topologicalSuspensionToSusp A
          (topologicalSuspensionPointIncl A PUnit.unit)) =
      topologicalSuspensionPointIncl A PUnit.unit
    rw [topologicalSuspensionToSusp_point,
      suspToTopologicalSuspension_south]
  · apply topologicalCone_hom_ext A
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro p
      rcases p with ⟨a, t⟩
      change suspToTopologicalSuspension A
          (topologicalSuspensionToSusp A
            (topologicalSuspensionConeIncl A
              (topologicalConeCylinderIncl A (a, t)))) =
        topologicalSuspensionConeIncl A
          (topologicalConeCylinderIncl A (a, t))
      rw [topologicalSuspensionToSusp_cone,
        topologicalConeToSusp_cylinder,
        suspToTopologicalSuspension_mk]
      rw [TopCat.I.homeomorph.{u}.symm_apply_apply]
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro p
      cases p
      change suspToTopologicalSuspension A
          (topologicalSuspensionToSusp A
            (topologicalSuspensionConeIncl A
              (topologicalConePointIncl A PUnit.unit))) =
        topologicalSuspensionConeIncl A
          (topologicalConePointIncl A PUnit.unit)
      rw [topologicalSuspensionToSusp_cone,
        topologicalConeToSusp_point,
        suspToTopologicalSuspension_north]

noncomputable def topologicalSuspensionIsoSusp :
    topologicalSuspension A ≅ TopCat.of (Susp A) where
  hom := topologicalSuspensionToSusp A
  inv := suspToTopologicalSuspension A
  hom_inv_id := topologicalSuspensionToSusp_comp_suspTo A
  inv_hom_id := suspToTopologicalSuspension_comp_toSusp A

noncomputable def topologicalSuspensionHomeomorphSusp :
    topologicalSuspension A ≃ₜ Susp A :=
  TopCat.homeoOfIso (topologicalSuspensionIsoSusp A)

def topologicalSuspensionMap {B : TopCat.{u}} (a : A ⟶ B) :
    topologicalSuspension A ⟶ topologicalSuspension B :=
  topologicalMappingConeMap (toUnit A) (toUnit B) a (𝟙 (𝟙_ TopCat)) (by
    simp)

variable {B : TopCat.{u}} [Nonempty B]

theorem topologicalConeToSusp_natural (a : A ⟶ B) :
    topologicalConeMap a ≫ topologicalConeToSusp B =
      topologicalConeToSusp A ≫ TopCat.ofHom (Susp.map a.hom) := by
  apply topologicalCone_hom_ext A
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    rcases p with ⟨x, t⟩
    simp only [ConcreteCategory.comp_apply]
    have hmap := ConcreteCategory.congr_hom
      (topologicalConeCylinderIncl_map a) (x, t)
    change topologicalConeMap a
        (topologicalConeCylinderIncl A (x, t)) =
      topologicalConeCylinderIncl B (a x, t) at hmap
    rw [hmap, topologicalConeToSusp_cylinder,
      topologicalConeToSusp_cylinder]
    rfl
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    simp only [ConcreteCategory.comp_apply]
    have hmap := ConcreteCategory.congr_hom
      (topologicalConePointIncl_map a) p
    simp only [ConcreteCategory.comp_apply] at hmap
    rw [hmap, topologicalConeToSusp_point,
      topologicalConeToSusp_point]
    change Susp.north B = Susp.map a.hom (Susp.north A)
    exact (Susp.map_north a.hom).symm

omit [Nonempty A] [Nonempty B] in
@[reassoc (attr := simp)]
theorem topologicalSuspensionPointIncl_map (a : A ⟶ B) :
    topologicalSuspensionPointIncl A ≫ topologicalSuspensionMap A a =
      topologicalSuspensionPointIncl B := by
  unfold topologicalSuspensionPointIncl topologicalSuspensionMap
    topologicalSuspension
  rw [topologicalMappingConeIncl_map, Category.id_comp]

omit [Nonempty A] [Nonempty B] in
@[reassoc (attr := simp)]
theorem topologicalSuspensionConeIncl_map (a : A ⟶ B) :
    topologicalSuspensionConeIncl A ≫ topologicalSuspensionMap A a =
      topologicalConeMap a ≫ topologicalSuspensionConeIncl B := by
  unfold topologicalSuspensionConeIncl topologicalSuspensionMap
    topologicalSuspension
  rw [topologicalMappingConeConeIncl_map]

theorem topologicalSuspensionToSusp_natural (a : A ⟶ B) :
    topologicalSuspensionMap A a ≫ topologicalSuspensionToSusp B =
      topologicalSuspensionToSusp A ≫ TopCat.ofHom (Susp.map a.hom) := by
  apply topologicalMappingCone_hom_ext (toUnit A)
  · change (topologicalSuspensionPointIncl A ≫
          topologicalSuspensionMap A a) ≫
        topologicalSuspensionToSusp B =
      (topologicalSuspensionPointIncl A ≫
          topologicalSuspensionToSusp A) ≫
        TopCat.ofHom (Susp.map a.hom)
    rw [topologicalSuspensionPointIncl_map,
      topologicalSuspensionPointIncl_toSusp B,
      topologicalSuspensionPointIncl_toSusp A]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    cases p
    simp only [ConcreteCategory.comp_apply]
    change Susp.south B = Susp.map a.hom (Susp.south A)
    exact (Susp.map_south a.hom).symm
  · change (topologicalSuspensionConeIncl A ≫
          topologicalSuspensionMap A a) ≫
        topologicalSuspensionToSusp B =
      (topologicalSuspensionConeIncl A ≫
          topologicalSuspensionToSusp A) ≫
        TopCat.ofHom (Susp.map a.hom)
    rw [topologicalSuspensionConeIncl_map]
    calc
      (topologicalConeMap a ≫ topologicalSuspensionConeIncl B) ≫
          topologicalSuspensionToSusp B =
        topologicalConeMap a ≫
          (topologicalSuspensionConeIncl B ≫
            topologicalSuspensionToSusp B) := Category.assoc _ _ _
      _ = topologicalConeMap a ≫ topologicalConeToSusp B := by
        rw [topologicalSuspensionConeIncl_toSusp]
      _ = topologicalConeToSusp A ≫
          TopCat.ofHom (Susp.map a.hom) :=
        topologicalConeToSusp_natural A a
      _ = (topologicalSuspensionConeIncl A ≫
            topologicalSuspensionToSusp A) ≫
          TopCat.ofHom (Susp.map a.hom) := by
        rw [topologicalSuspensionConeIncl_toSusp]

end Submission
