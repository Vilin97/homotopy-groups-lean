/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.MappingCone
import Submission.WhiteheadTheorem.HEP.Cofibration

/-!
# The target inclusion in a mapping cone is a cofibration

The target summand of a mapping cone has a canonical collar.  A homotopy on that summand
extends by using the homotopy inside the lower half of the cone cylinder and rescaling the
remaining cylinder back onto the whole cone.  The rescaling fixes the cone point, so it descends
through both pushout quotients.
-/

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory
  CartesianMonoidalCategory
open scoped Topology TopCat unitInterval

noncomputable section

namespace Submission

universe u

/-! ### Collar coordinates -/

/-- Time remaining after a cone point of height `s` has spent time `2s` traversing the lower
collar. -/
def mappingConeCollarHomotopyTime (s : TopCat.I.{u}) (t : unitInterval) : unitInterval :=
  Set.projIcc (0 : ℝ) 1 zero_le_one
    ((t : ℝ) - 2 * (TopCat.I.homeomorph s : ℝ))

/-- Rescale the part of the cone above the active collar back onto the whole cone. -/
def mappingConeCollarHeight (s : TopCat.I.{u}) (t : unitInterval) : TopCat.I.{u} :=
  TopCat.I.homeomorph.symm <|
    Set.projIcc (0 : ℝ) 1 zero_le_one
      ((2 * (TopCat.I.homeomorph s : ℝ) - (t : ℝ)) / (2 - (t : ℝ)))

@[fun_prop]
theorem continuous_mappingConeCollarHomotopyTime :
    Continuous fun p : TopCat.I.{u} × unitInterval ↦
      mappingConeCollarHomotopyTime p.1 p.2 :=
  continuous_projIcc.comp' (by fun_prop)

@[fun_prop]
theorem continuous_mappingConeCollarHeight :
    Continuous fun p : TopCat.I.{u} × unitInterval ↦
      mappingConeCollarHeight p.1 p.2 := by
  apply TopCat.I.homeomorph.symm.continuous.comp
  apply continuous_projIcc.comp
  refine Continuous.div (by fun_prop) (by fun_prop) fun p ↦ ?_
  have ht := p.2.property.2
  linarith

@[simp]
theorem mappingConeCollarHomotopyTime_zero (t : unitInterval) :
    mappingConeCollarHomotopyTime (0 : TopCat.I.{u}) t = t := by
  apply Subtype.ext
  change ↑(Set.projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) - 2 * 0)) = (t : ℝ)
  norm_num

theorem mappingConeCollarHomotopyTime_eq_zero_of_eq
    (s : TopCat.I.{u}) (t : unitInterval)
    (hst : 2 * (TopCat.I.homeomorph s : ℝ) = (t : ℝ)) :
    mappingConeCollarHomotopyTime s t = 0 := by
  apply Subtype.ext
  simp [mappingConeCollarHomotopyTime, Set.projIcc, hst]

@[simp]
theorem mappingConeCollarHeight_zero (s : TopCat.I.{u}) :
    mappingConeCollarHeight s 0 = s := by
  apply TopCat.I.homeomorph.injective
  apply Subtype.ext
  change ↑(Set.projIcc (0 : ℝ) 1 zero_le_one
    ((2 * (TopCat.I.homeomorph s : ℝ) - 0) / (2 - 0))) =
      (TopCat.I.homeomorph s : ℝ)
  have h : (2 * (TopCat.I.homeomorph s : ℝ) - 0) / (2 - 0) =
      (TopCat.I.homeomorph s : ℝ) := by ring
  rw [h, Set.projIcc_val]

theorem mappingConeCollarHeight_eq_zero_of_eq
    (s : TopCat.I.{u}) (t : unitInterval)
    (hst : 2 * (TopCat.I.homeomorph s : ℝ) = (t : ℝ)) :
    mappingConeCollarHeight s t = 0 := by
  apply TopCat.I.homeomorph.injective
  apply Subtype.ext
  simp [mappingConeCollarHeight, Set.projIcc, hst]

@[simp]
theorem mappingConeCollarHeight_one (t : unitInterval) :
    mappingConeCollarHeight (1 : TopCat.I.{u}) t = 1 := by
  apply TopCat.I.homeomorph.injective
  rw [mappingConeCollarHeight, Homeomorph.apply_symm_apply]
  rw [show TopCat.I.homeomorph (1 : TopCat.I.{u}) = (1 : unitInterval) from
    TopCat.I.homeomorph_one.{u}]
  apply Subtype.ext
  have hden : (2 : ℝ) - (t : ℝ) ≠ 0 := by
    have ht := t.property.2
    linarith
  have hratio : ((2 : ℝ) - (t : ℝ)) / (2 - (t : ℝ)) = 1 :=
    div_self hden
  norm_num
  rw [hratio]

/-! ### The explicit extension -/

variable {A X Y : TopCat.{u}}

set_option maxHeartbeats 800000 in
/-- The cone-cylinder part of the homotopy extension at time `t`. -/
def topologicalMappingConeHEPCylinderAt (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩)
    (t : unitInterval) : (A ⊗ TopCat.I : TopCat.{u}) ⟶ Y :=
  ConcreteCategory.ofHom (C := TopCat) {
    toFun := fun p ↦
      if 2 * (TopCat.I.homeomorph p.2 : ℝ) ≤ (t : ℝ) then
        H (f p.1, mappingConeCollarHomotopyTime p.2 t)
      else
        g (topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A
            (p.1, mappingConeCollarHeight p.2 t)))
    continuous_toFun := by
      apply Continuous.if_le
      · exact H.continuous.comp
          ((f.hom.continuous.comp continuous_fst).prodMk
            (continuous_mappingConeCollarHomotopyTime.comp
              (continuous_snd.prodMk (continuous_const :
                Continuous fun _ : (A ⊗ TopCat.I : TopCat.{u}) ↦ t))))
      · exact g.continuous.comp
          ((topologicalMappingConeConeIncl f).hom.continuous.comp
            ((topologicalConeCylinderIncl A).hom.continuous.comp
              (continuous_fst.prodMk
                (continuous_mappingConeCollarHeight.comp
                  (continuous_snd.prodMk (continuous_const :
                    Continuous fun _ : (A ⊗ TopCat.I : TopCat.{u}) ↦ t))))))
      · exact (continuous_const.mul
          (continuous_subtype_val.comp
            (TopCat.I.homeomorph.continuous.comp continuous_snd)))
      · exact continuous_const
      · intro p hp
        rw [mappingConeCollarHomotopyTime_eq_zero_of_eq p.2 t hp,
          mappingConeCollarHeight_eq_zero_of_eq p.2 t hp]
        have hpoint := congrArg (fun k ↦ k (f p.1)) hcompat
        change g (topologicalMappingConeIncl f (f p.1)) = H (f p.1, 0) at hpoint
        rw [show topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A (p.1, 0)) =
          topologicalMappingConeIncl f (f p.1) by
            exact ConcreteCategory.congr_hom
              (topologicalMappingCone_condition f).symm p.1]
        exact hpoint.symm }

/-- The time-`t` slice of a homotopy on the target summand. -/
def topologicalMappingConeHEPRestrictionAt (H : C(X × unitInterval, Y))
    (t : unitInterval) : X ⟶ Y :=
  ConcreteCategory.ofHom (C := TopCat)
    ⟨fun x ↦ H (x, t), H.continuous.comp
      (continuous_id.prodMk continuous_const)⟩

/-- The cone part of the homotopy extension at time `t`. -/
def topologicalMappingConeHEPConeAt (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩)
    (t : unitInterval) : topologicalCone A ⟶ Y :=
  topologicalConeDesc A
    (topologicalMappingConeHEPCylinderAt f g H hcompat t)
    (topologicalConePointIncl A ≫ topologicalMappingConeConeIncl f ≫
      TopCat.ofHom g) (by
        apply TopCat.hom_ext
        ext a
        simp only [ConcreteCategory.comp_apply]
        change topologicalMappingConeHEPCylinderAt f g H hcompat t
          (TopCat.ι₁ a) = _
        rw [TopCat.ι₁_apply]
        simp only [topologicalMappingConeHEPCylinderAt,
          ConcreteCategory.hom_ofHom]
        change (if 2 * (TopCat.I.homeomorph (1 : TopCat.I.{u}) : ℝ) ≤ (t : ℝ)
          then _ else _) = _
        rw [if_neg (by
          rw [TopCat.I.homeomorph_one.{u}]
          have ht := t.property.2
          norm_num
          linarith), mappingConeCollarHeight_one]
        have hc := ConcreteCategory.congr_hom (pushout.condition :
          (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) ≫ topologicalConeCylinderIncl A =
            toUnit A ≫ topologicalConePointIncl A) a
        exact congrArg
          (fun c ↦ g (topologicalMappingConeConeIncl f c)) hc)

/-- On the cone base, the extended cone map agrees with the time-`t` restriction of the given
homotopy. -/
theorem topologicalMappingConeHEPConeAt_base (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩)
    (t : unitInterval) :
    f ≫ topologicalMappingConeHEPRestrictionAt H t =
      topologicalConeBaseIncl A ≫
        topologicalMappingConeHEPConeAt f g H hcompat t := by
  rw [topologicalConeBaseIncl, Category.assoc,
    topologicalMappingConeHEPConeAt, topologicalConeCylinderIncl_desc]
  apply TopCat.hom_ext
  ext a
  simp only [ConcreteCategory.comp_apply]
  rw [TopCat.ι₀_apply]
  simp only [topologicalMappingConeHEPCylinderAt,
    ConcreteCategory.hom_ofHom]
  change H (f a, t) =
    if 2 * (TopCat.I.homeomorph (0 : TopCat.I.{u}) : ℝ) ≤ (t : ℝ)
      then _ else _
  rw [if_pos (by simpa using t.property.1),
    mappingConeCollarHomotopyTime_zero]

/-- The full mapping-cone homotopy extension at time `t`. -/
def topologicalMappingConeHEPExtensionAt (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩)
    (t : unitInterval) : topologicalMappingCone f ⟶ Y :=
  pushout.desc
    (topologicalMappingConeHEPRestrictionAt H t)
    (topologicalMappingConeHEPConeAt f g H hcompat t)
    (topologicalMappingConeHEPConeAt_base f g H hcompat t)

@[reassoc (attr := simp)]
theorem topologicalMappingConeIncl_HEPExtensionAt (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩)
    (t : unitInterval) :
    topologicalMappingConeIncl f ≫
        topologicalMappingConeHEPExtensionAt f g H hcompat t =
      topologicalMappingConeHEPRestrictionAt H t :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem topologicalMappingConeConeIncl_HEPExtensionAt (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩)
    (t : unitInterval) :
    topologicalMappingConeConeIncl f ≫
        topologicalMappingConeHEPExtensionAt f g H hcompat t =
      topologicalMappingConeHEPConeAt f g H hcompat t :=
  pushout.inr_desc _ _ _

@[simp]
theorem topologicalMappingConeHEPExtensionAt_incl (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩)
    (t : unitInterval) (x : X) :
    topologicalMappingConeHEPExtensionAt f g H hcompat t
        (topologicalMappingConeIncl f x) = H (x, t) := by
  exact ConcreteCategory.congr_hom
    (topologicalMappingConeIncl_HEPExtensionAt f g H hcompat t) x

@[simp]
theorem topologicalMappingConeHEPExtensionAt_cylinder (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩)
    (t : unitInterval) (p : (A ⊗ TopCat.I : TopCat.{u})) :
    topologicalMappingConeHEPExtensionAt f g H hcompat t
        (topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A p)) =
      topologicalMappingConeHEPCylinderAt f g H hcompat t p := by
  calc
    _ = topologicalMappingConeHEPConeAt f g H hcompat t
        (topologicalConeCylinderIncl A p) :=
      ConcreteCategory.congr_hom
        (topologicalMappingConeConeIncl_HEPExtensionAt f g H hcompat t)
          (topologicalConeCylinderIncl A p)
    _ = _ := ConcreteCategory.congr_hom
      (topologicalConeCylinderIncl_desc A _ _ _) p

@[simp]
theorem topologicalMappingConeHEPExtensionAt_conePoint (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩)
    (t : unitInterval) (z : 𝟙_ TopCat.{u}) :
    topologicalMappingConeHEPExtensionAt f g H hcompat t
        (topologicalMappingConeConeIncl f
          (topologicalConePointIncl A z)) =
      g (topologicalMappingConeConeIncl f
        (topologicalConePointIncl A z)) := by
  calc
    _ = topologicalMappingConeHEPConeAt f g H hcompat t
        (topologicalConePointIncl A z) :=
      ConcreteCategory.congr_hom
        (topologicalMappingConeConeIncl_HEPExtensionAt f g H hcompat t)
          (topologicalConePointIncl A z)
    _ = _ := ConcreteCategory.congr_hom
      (topologicalConePointIncl_desc A _ _ _) z

set_option maxHeartbeats 1200000 in
/-- The explicit mapping-cone extension varies continuously with time. -/
theorem continuous_topologicalMappingConeHEPExtensionAt (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩) :
    Continuous fun p : unitInterval × topologicalMappingCone f ↦
      topologicalMappingConeHEPExtensionAt f g H hcompat p.1 p.2 := by
  apply (topologicalMappingConeTripleDesc_isQuotientMap f).continuous_lift_prod_right
  let L : (unitInterval × (A ⊗ TopCat.I : TopCat.{u})) ⊕
      (unitInterval × (𝟙_ TopCat.{u})) → Y :=
    Sum.elim
      (fun p ↦
        if 2 * (TopCat.I.homeomorph p.2.2 : ℝ) ≤ (p.1 : ℝ) then
          H (f p.2.1, mappingConeCollarHomotopyTime p.2.2 p.1)
        else
          g (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A
              (p.2.1, mappingConeCollarHeight p.2.2 p.1))))
      (fun p ↦ g (topologicalMappingConeConeIncl f
        (topologicalConePointIncl A p.2)))
  have hL : Continuous L := by
    rw [continuous_sum_dom]
    constructor
    · dsimp [L]
      apply Continuous.if_le
      · exact H.continuous.comp
          ((f.hom.continuous.comp
              ((fst A TopCat.I).hom.continuous.comp continuous_snd)).prodMk
            (continuous_mappingConeCollarHomotopyTime.comp
              (((snd A TopCat.I).hom.continuous.comp continuous_snd).prodMk
                continuous_fst)))
      · exact g.continuous.comp
          ((topologicalMappingConeConeIncl f).hom.continuous.comp
            ((topologicalConeCylinderIncl A).hom.continuous.comp
              (((fst A TopCat.I).hom.continuous.comp continuous_snd).prodMk
                (continuous_mappingConeCollarHeight.comp
                  (((snd A TopCat.I).hom.continuous.comp continuous_snd).prodMk
                    continuous_fst)))))
      · exact continuous_const.mul
          (continuous_subtype_val.comp
            (TopCat.I.homeomorph.continuous.comp
              ((snd A TopCat.I).hom.continuous.comp continuous_snd)))
      · exact continuous_subtype_val.comp continuous_fst
      · intro p hp
        rw [mappingConeCollarHomotopyTime_eq_zero_of_eq p.2.2 p.1 hp,
          mappingConeCollarHeight_eq_zero_of_eq p.2.2 p.1 hp]
        have hpoint := congrArg (fun k ↦ k (f p.2.1)) hcompat
        change g (topologicalMappingConeIncl f (f p.2.1)) =
          H (f p.2.1, 0) at hpoint
        rw [show topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A (p.2.1, 0)) =
          topologicalMappingConeIncl f (f p.2.1) by
            exact ConcreteCategory.congr_hom
              (topologicalMappingCone_condition f).symm p.2.1]
        exact hpoint.symm
    · dsimp [L]
      fun_prop
  have hright : Continuous (fun p : unitInterval ×
      ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u})) ↦
      match p.2 with
      | Sum.inl c =>
          if 2 * (TopCat.I.homeomorph c.2 : ℝ) ≤ (p.1 : ℝ) then
            H (f c.1, mappingConeCollarHomotopyTime c.2 p.1)
          else
            g (topologicalMappingConeConeIncl f
              (topologicalConeCylinderIncl A
                (c.1, mappingConeCollarHeight c.2 p.1)))
      | Sum.inr z => g (topologicalMappingConeConeIncl f
          (topologicalConePointIncl A z))) := by
    have hcomp := hL.comp (Homeomorph.prodSumDistrib :
      unitInterval × ((A ⊗ TopCat.I : TopCat.{u}) ⊕
        (𝟙_ TopCat.{u})) ≃ₜ _).continuous
    convert hcomp using 1
    funext p
    rcases p with ⟨t, c | z⟩ <;> rfl
  let K : (unitInterval × (X : Type u)) ⊕
      (unitInterval × ((A ⊗ TopCat.I : TopCat.{u}) ⊕
        (𝟙_ TopCat.{u}))) → Y :=
    Sum.elim (fun p ↦ H (p.2, p.1))
      (fun p ↦ match p.2 with
        | Sum.inl c =>
            if 2 * (TopCat.I.homeomorph c.2 : ℝ) ≤ (p.1 : ℝ) then
              H (f c.1, mappingConeCollarHomotopyTime c.2 p.1)
            else
              g (topologicalMappingConeConeIncl f
                (topologicalConeCylinderIncl A
                  (c.1, mappingConeCollarHeight c.2 p.1)))
        | Sum.inr z => g (topologicalMappingConeConeIncl f
            (topologicalConePointIncl A z)))
  have hK : Continuous K := by
    rw [continuous_sum_dom]
    exact ⟨by dsimp [K]; fun_prop, by simpa [K] using hright⟩
  have hcomp := hK.comp (Homeomorph.prodSumDistrib :
    unitInterval × ((X : Type u) ⊕ ((A ⊗ TopCat.I : TopCat.{u}) ⊕
      (𝟙_ TopCat.{u}))) ≃ₜ _).continuous
  convert hcomp using 1
  funext p
  rcases p with ⟨t, x | r⟩
  · change topologicalMappingConeHEPExtensionAt f g H hcompat t
      (topologicalMappingConeIncl f x) =
        K (Homeomorph.prodSumDistrib (t, Sum.inl x))
    rw [show (Homeomorph.prodSumDistrib (t, Sum.inl x) :
      (unitInterval × (X : Type u)) ⊕ _) = Sum.inl (t, x) from rfl]
    simp [K]
  · rcases r with c | z
    · change topologicalMappingConeHEPExtensionAt f g H hcompat t
        (topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A c)) =
            K (Homeomorph.prodSumDistrib (t, Sum.inr (Sum.inl c)))
      rw [show (Homeomorph.prodSumDistrib (t, Sum.inr (Sum.inl c)) :
        (unitInterval × (X : Type u)) ⊕ _) =
          Sum.inr (t, Sum.inl c) from rfl]
      simp [K, topologicalMappingConeHEPCylinderAt]
    · change topologicalMappingConeHEPExtensionAt f g H hcompat t
        (topologicalMappingConeConeIncl f
          (topologicalConePointIncl A z)) =
            K (Homeomorph.prodSumDistrib (t, Sum.inr (Sum.inr z)))
      rw [show (Homeomorph.prodSumDistrib (t, Sum.inr (Sum.inr z)) :
        (unitInterval × (X : Type u)) ⊕ _) =
          Sum.inr (t, Sum.inr z) from rfl]
      simp [K]

/-- At time zero, the explicit extension is the original map on the mapping cone. -/
theorem topologicalMappingConeHEPExtensionAt_zero (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩) :
    topologicalMappingConeHEPExtensionAt f g H hcompat 0 =
      TopCat.ofHom g := by
  apply topologicalMappingCone_hom_ext f
  · apply TopCat.hom_ext
    ext x
    simp only [ConcreteCategory.comp_apply,
      topologicalMappingConeHEPExtensionAt_incl]
    have hpoint := congrArg (fun k ↦ k x) hcompat
    exact hpoint.symm
  · apply topologicalCone_hom_ext A
    · apply TopCat.hom_ext
      ext p
      rcases p with ⟨a, s⟩
      simp only [ConcreteCategory.comp_apply,
        topologicalMappingConeHEPExtensionAt_cylinder,
        topologicalMappingConeHEPCylinderAt,
        ConcreteCategory.hom_ofHom]
      change (if 2 * (TopCat.I.homeomorph s : ℝ) ≤ (0 : ℝ) then
          H (f a, mappingConeCollarHomotopyTime s 0)
        else
          g (topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A
              (a, mappingConeCollarHeight s 0)))) =
        g (topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A (a, s)))
      by_cases hcollar :
          2 * (TopCat.I.homeomorph s : ℝ) ≤ (0 : ℝ)
      · rw [if_pos hcollar]
        have hsval : (TopCat.I.homeomorph s : ℝ) = 0 := by
          have hsnonneg := (TopCat.I.homeomorph s).property.1
          linarith
        have hs : s = 0 := by
          apply TopCat.I.homeomorph.injective
          apply Subtype.ext
          simpa [TopCat.I.homeomorph_zero.{u}] using hsval
        subst s
        rw [mappingConeCollarHomotopyTime_zero]
        have hpoint := congrArg (fun k ↦ k (f a)) hcompat
        change g (topologicalMappingConeIncl f (f a)) = H (f a, 0) at hpoint
        rw [show topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A (a, 0)) =
          topologicalMappingConeIncl f (f a) by
            exact ConcreteCategory.congr_hom
              (topologicalMappingCone_condition f).symm a]
        exact hpoint.symm
      · rw [if_neg hcollar, mappingConeCollarHeight_zero]
    · apply TopCat.hom_ext
      ext z
      simp only [ConcreteCategory.comp_apply,
        topologicalMappingConeHEPExtensionAt_conePoint]
      rfl

/-- The uncurried homotopy extension supplied by the canonical collar of a mapping cone. -/
def topologicalMappingConeHEPExtension (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩) :
    C(topologicalMappingCone f × unitInterval, Y) :=
  ⟨fun p ↦ topologicalMappingConeHEPExtensionAt f g H hcompat p.2 p.1,
    (continuous_topologicalMappingConeHEPExtensionAt f g H hcompat).comp
      (continuous_snd.prodMk continuous_fst)⟩

theorem topologicalMappingConeHEPExtension_bottom (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩) :
    g = (topologicalMappingConeHEPExtension f g H hcompat).comp
      ⟨fun z ↦ (z, 0), by fun_prop⟩ := by
  ext z
  change g z = topologicalMappingConeHEPExtensionAt f g H hcompat 0 z
  exact (ConcreteCategory.congr_hom
    (topologicalMappingConeHEPExtensionAt_zero f g H hcompat) z).symm

theorem topologicalMappingConeHEPExtension_wall (f : A ⟶ X)
    (g : C(topologicalMappingCone f, Y)) (H : C(X × unitInterval, Y))
    (hcompat : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩) :
    H = (topologicalMappingConeHEPExtension f g H hcompat).comp
      ((topologicalMappingConeIncl f).hom.prodMap
        (ContinuousMap.id unitInterval)) := by
  ext p
  rcases p with ⟨x, t⟩
  change H (x, t) = topologicalMappingConeHEPExtensionAt f g H hcompat t
    (topologicalMappingConeIncl f x)
  exact (topologicalMappingConeHEPExtensionAt_incl f g H hcompat t x).symm

/-- The target inclusion `X → C_f` has the homotopy extension property. -/
theorem topologicalMappingConeIncl_hasHomotopyExtensionProperty (f : A ⟶ X)
    (Y : TopCat.{u}) :
    HasHomotopyExtensionProperty (topologicalMappingConeIncl f).hom Y := by
  intro g H hcompat
  have hcompat' : g.comp (topologicalMappingConeIncl f).hom =
      H.comp ⟨fun x ↦ (x, 0), by fun_prop⟩ := by
    ext x
    exact congrFun hcompat x
  refine ⟨topologicalMappingConeHEPExtension f g H hcompat', ?_, ?_⟩
  · funext z
    exact congrArg (fun k ↦ k z)
      (topologicalMappingConeHEPExtension_bottom f g H hcompat')
  · funext p
    rcases p with ⟨x, t⟩
    exact (topologicalMappingConeHEPExtensionAt_incl
      f g H hcompat' t x).symm

/-- The target inclusion into a topological mapping cone is a cofibration. -/
instance topologicalMappingConeIncl_isCofibration (f : A ⟶ X) :
    IsCofibration (topologicalMappingConeIncl f) :=
  (IsCofibration.iff_hasHomotopyExtensionProperty
    (topologicalMappingConeIncl f)).mpr fun Y ↦
      topologicalMappingConeIncl_hasHomotopyExtensionProperty f Y

end Submission
