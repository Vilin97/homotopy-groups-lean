/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.MappingCone

/-!
# The standard open cover of a mapping cone

The height coordinate gives a lower collar containing the original space and an upper collar
containing the cone point.  Thresholds `2/3` and `1/3` make both pieces open and make their
union the whole mapping cone.  These sets are the cover used in the mapping-cone
Mayer--Vietoris and excision arguments.
-/

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory CartesianMonoidalCategory

noncomputable section

namespace Submission

universe u v

variable {A X : TopCat.{u}}

/-- Mapping-cone height as a real number in the unit interval. -/
def topologicalMappingConeHeightReal (f : A ⟶ X) :
    topologicalMappingCone f → ℝ := fun p ↦
  (TopCat.I.homeomorph (topologicalMappingConeHeight f p) : ℝ)

theorem continuous_topologicalMappingConeHeightReal (f : A ⟶ X) :
    Continuous (topologicalMappingConeHeightReal f) := by
  unfold topologicalMappingConeHeightReal
  fun_prop

@[simp]
theorem topologicalMappingConeTripleDesc_inl_heightReal (f : A ⟶ X) (x : X) :
    topologicalMappingConeHeightReal f
      (topologicalMappingConeTripleDesc f (Sum.inl x)) = 0 := by
  unfold topologicalMappingConeHeightReal
  change (TopCat.I.homeomorph
    (topologicalMappingConeHeight f (topologicalMappingConeIncl f x)) : ℝ) = 0
  rw [show topologicalMappingConeHeight f (topologicalMappingConeIncl f x) = 0 from
    ConcreteCategory.congr_hom (topologicalMappingConeIncl_height f) x]
  simp

@[simp]
theorem topologicalMappingConeTripleDesc_cylinder_heightReal (f : A ⟶ X)
    (c : (A ⊗ TopCat.I : TopCat.{u})) :
    topologicalMappingConeHeightReal f
      (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))) =
      (TopCat.I.homeomorph c.2 : ℝ) := by
  unfold topologicalMappingConeHeightReal
  change (TopCat.I.homeomorph
    (topologicalMappingConeHeight f
      (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c))) : ℝ) = _
  rw [show topologicalMappingConeHeight f
      (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c)) =
      topologicalConeHeight A (topologicalConeCylinderIncl A c) from
    ConcreteCategory.congr_hom (topologicalMappingConeConeIncl_height f) _]
  rw [show topologicalConeHeight A (topologicalConeCylinderIncl A c) = c.2 from
    ConcreteCategory.congr_hom (topologicalConeCylinderIncl_height A) c]

@[simp]
theorem topologicalMappingConeTripleDesc_point_heightReal (f : A ⟶ X)
    (z : (𝟙_ TopCat.{u} : TopCat.{u})) :
    topologicalMappingConeHeightReal f
      (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inr z))) = 1 := by
  unfold topologicalMappingConeHeightReal
  change (TopCat.I.homeomorph
    (topologicalMappingConeHeight f
      (topologicalMappingConeConeIncl f (topologicalConePointIncl A z))) : ℝ) = 1
  rw [show topologicalMappingConeHeight f
      (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
      topologicalConeHeight A (topologicalConePointIncl A z) from
    ConcreteCategory.congr_hom (topologicalMappingConeConeIncl_height f) _]
  rw [show topologicalConeHeight A (topologicalConePointIncl A z) = 1 from
    ConcreteCategory.congr_hom (topologicalConePointIncl_height A) z]
  simp

/-- The cone-cylinder quotient is injective away from its collapsed top end. -/
theorem topologicalConeCylinderIncl_eq_iff_below
    (c d : (A ⊗ TopCat.I : TopCat.{u}))
    (hc : (TopCat.I.homeomorph c.2 : ℝ) < 2 / 3)
    (h : topologicalConeCylinderIncl A c = topologicalConeCylinderIncl A d) : c = d := by
  let q := (forget TopCat).map (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I)
  have hpo := (IsPushout.of_isColimit
    (pushoutIsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) (toUnit A))).map (forget TopCat)
  have hq : Function.Injective q := fun _ _ hxy ↦ congrArg Prod.fst hxy
  change hpo.cocone.inl c = hpo.cocone.inl d at h
  rcases (pushoutCocone_inl_eq_inl_iff_of_isColimit hpo.isColimit hq c d).mp h with
    hcd | ⟨s, t, hst, hcs, hdt⟩
  · exact hcd
  · have hc1 : c.2 = 1 := congrArg Prod.snd hcs
    have hc1' : (TopCat.I.homeomorph c.2 : ℝ) = 1 := by
      rw [hc1]
      simp
    linarith

/-- A cylinder point below the cone apex can equal a base point only at height zero. -/
theorem topologicalConeCylinderIncl_eq_baseIncl_below
    (c : (A ⊗ TopCat.I : TopCat.{u})) (a : A)
    (hc : (TopCat.I.homeomorph c.2 : ℝ) < 2 / 3)
    (h : topologicalConeCylinderIncl A c = topologicalConeBaseIncl A a) :
    c = (a, 0) := by
  apply topologicalConeCylinderIncl_eq_iff_below c (a, 0) hc
  simpa [topologicalConeBaseIncl] using h

/-- In the lower collar, a point of the original space equals a cylinder point precisely as
dictated by the attaching map. -/
theorem topologicalMappingConeIncl_eq_cylinder_below
    (f : A ⟶ X) (x : X) (c : (A ⊗ TopCat.I : TopCat.{u}))
    (hc : (TopCat.I.homeomorph c.2 : ℝ) < 2 / 3)
    (h : topologicalMappingConeIncl f x =
      topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c)) :
    x = f c.1 := by
  let q := (forget TopCat).map (topologicalConeBaseIncl A)
  have hpo := ((IsPushout.of_isColimit
    (pushoutIsPushout f (topologicalConeBaseIncl A))).flip.map (forget TopCat))
  have hq : Function.Injective q :=
    (TopCat.mono_iff_injective (topologicalConeBaseIncl A)).mp inferInstance
  change hpo.cocone.inr x = hpo.cocone.inl (topologicalConeCylinderIncl A c) at h
  rcases (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit hpo.isColimit hq
    (topologicalConeCylinderIncl A c) x).mp h.symm with ⟨a, ha, hfa⟩
  have hc0 : c = (a, 0) :=
    topologicalConeCylinderIncl_eq_baseIncl_below c a hc ha.symm
  rw [hc0]
  exact hfa.symm

/-- Cylinder points identified in the lower mapping-cone collar have the same image under the
attaching map. -/
theorem topologicalMappingConeCylinder_eq_below
    (f : A ⟶ X) (c d : (A ⊗ TopCat.I : TopCat.{u}))
    (hc : (TopCat.I.homeomorph c.2 : ℝ) < 2 / 3)
    (hd : (TopCat.I.homeomorph d.2 : ℝ) < 2 / 3)
    (h : topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c) =
      topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A d)) :
    f c.1 = f d.1 := by
  let q := (forget TopCat).map (topologicalConeBaseIncl A)
  have hpo := ((IsPushout.of_isColimit
    (pushoutIsPushout f (topologicalConeBaseIncl A))).flip.map (forget TopCat))
  have hq : Function.Injective q :=
    (TopCat.mono_iff_injective (topologicalConeBaseIncl A)).mp inferInstance
  change hpo.cocone.inl (topologicalConeCylinderIncl A c) =
    hpo.cocone.inl (topologicalConeCylinderIncl A d) at h
  rcases (pushoutCocone_inl_eq_inl_iff_of_isColimit hpo.isColimit hq
    (topologicalConeCylinderIncl A c) (topologicalConeCylinderIncl A d)).mp h with
    hcone | ⟨a, b, hab, hca, hdb⟩
  · exact congrArg (fun z : (A ⊗ TopCat.I : TopCat.{u}) ↦ f z.1)
      (topologicalConeCylinderIncl_eq_iff_below c d hc hcone)
  · have hc0 : c = (a, 0) :=
      topologicalConeCylinderIncl_eq_baseIncl_below c a hc hca
    have hd0 : d = (b, 0) :=
      topologicalConeCylinderIncl_eq_baseIncl_below d b hd hdb
    simpa [hc0, hd0] using hab

/-- Equality of an original-space point with a cylinder point forces the latter to have height
zero. -/
theorem topologicalMappingConeIncl_eq_cylinder_height_zero
    (f : A ⟶ X) (x : X) (c : (A ⊗ TopCat.I : TopCat.{u}))
    (h : topologicalMappingConeIncl f x =
      topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c)) :
    c.2 = 0 := by
  have hh := congrArg (topologicalMappingConeHeight f) h
  change (topologicalMappingConeHeight f (topologicalMappingConeIncl f x)) =
    topologicalMappingConeHeight f
      (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c)) at hh
  rw [show topologicalMappingConeHeight f (topologicalMappingConeIncl f x) = 0 from
    ConcreteCategory.congr_hom (topologicalMappingConeIncl_height f) x] at hh
  rw [show topologicalMappingConeHeight f
      (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c)) =
      topologicalConeHeight A (topologicalConeCylinderIncl A c) from
    ConcreteCategory.congr_hom (topologicalMappingConeConeIncl_height f) _] at hh
  rw [show topologicalConeHeight A (topologicalConeCylinderIncl A c) = c.2 from
    ConcreteCategory.congr_hom (topologicalConeCylinderIncl_height A) c] at hh
  exact hh.symm

/-- Scaling a lower cylinder point toward its base preserves an equality with the original
space. -/
theorem topologicalMappingConeIncl_eq_scaledCylinder
    (f : A ⟶ X) (x : X) (c : (A ⊗ TopCat.I : TopCat.{u})) (t : TopCat.I)
    (h : topologicalMappingConeIncl f x =
      topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c)) :
    topologicalMappingConeIncl f x = topologicalMappingConeConeIncl f
      (topologicalConeCylinderIncl A (c.1, TopCat.I.min (c.2, t))) := by
  have hc0 := topologicalMappingConeIncl_eq_cylinder_height_zero f x c h
  have hc : c = (c.1, 0) := Prod.ext rfl hc0
  rw [hc] at h ⊢
  simpa using h

/-- Two equal lower cylinder points are either represented by the same cylinder point or both
lie at height zero, where the attaching map performs the identification. -/
theorem topologicalMappingConeCylinder_eq_or_height_zero
    (f : A ⟶ X) (c d : (A ⊗ TopCat.I : TopCat.{u}))
    (hc : (TopCat.I.homeomorph c.2 : ℝ) < 2 / 3)
    (hd : (TopCat.I.homeomorph d.2 : ℝ) < 2 / 3)
    (h : topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c) =
      topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A d)) :
    c = d ∨ (c.2 = 0 ∧ d.2 = 0) := by
  let q := (forget TopCat).map (topologicalConeBaseIncl A)
  have hpo := ((IsPushout.of_isColimit
    (pushoutIsPushout f (topologicalConeBaseIncl A))).flip.map (forget TopCat))
  have hq : Function.Injective q :=
    (TopCat.mono_iff_injective (topologicalConeBaseIncl A)).mp inferInstance
  change hpo.cocone.inl (topologicalConeCylinderIncl A c) =
    hpo.cocone.inl (topologicalConeCylinderIncl A d) at h
  rcases (pushoutCocone_inl_eq_inl_iff_of_isColimit hpo.isColimit hq
    (topologicalConeCylinderIncl A c) (topologicalConeCylinderIncl A d)).mp h with
    hcone | ⟨a, b, hab, hca, hdb⟩
  · exact Or.inl (topologicalConeCylinderIncl_eq_iff_below c d hc hcone)
  · right
    have hc0 : c = (a, 0) :=
      topologicalConeCylinderIncl_eq_baseIncl_below c a hc hca
    have hd0 : d = (b, 0) :=
      topologicalConeCylinderIncl_eq_baseIncl_below d b hd hdb
    exact ⟨by rw [hc0], by rw [hd0]⟩

/-- Simultaneously scaling two equal lower cylinder points toward their bases preserves their
equality in the mapping cone. -/
theorem topologicalMappingConeScaledCylinder_eq
    (f : A ⟶ X) (c d : (A ⊗ TopCat.I : TopCat.{u}))
    (hc : (TopCat.I.homeomorph c.2 : ℝ) < 2 / 3)
    (hd : (TopCat.I.homeomorph d.2 : ℝ) < 2 / 3) (t : TopCat.I)
    (h : topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c) =
      topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A d)) :
    topologicalMappingConeConeIncl f
        (topologicalConeCylinderIncl A (c.1, TopCat.I.min (c.2, t))) =
      topologicalMappingConeConeIncl f
        (topologicalConeCylinderIncl A (d.1, TopCat.I.min (d.2, t))) := by
  rcases topologicalMappingConeCylinder_eq_or_height_zero f c d hc hd h with
    hcd | ⟨hc0, hd0⟩
  · rw [hcd]
  · have hc' : c = (c.1, 0) := Prod.ext rfl hc0
    have hd' : d = (d.1, 0) := Prod.ext rfl hd0
    rw [hc', hd'] at h ⊢
    simpa using h

/-- The cone summand embeds in the mapping cone away from height zero.  The only extra
identifications made by the outer pushout occur along the cone base. -/
theorem topologicalMappingConeConeIncl_eq_of_height_pos
    (f : A ⟶ X) (p q : topologicalCone A)
    (hp : 0 < topologicalMappingConeHeightReal f (topologicalMappingConeConeIncl f p))
    (h : topologicalMappingConeConeIncl f p = topologicalMappingConeConeIncl f q) :
    p = q := by
  let b := (forget TopCat).map (topologicalConeBaseIncl A)
  have hpo := ((IsPushout.of_isColimit
    (pushoutIsPushout f (topologicalConeBaseIncl A))).flip.map (forget TopCat))
  have hb : Function.Injective b :=
    (TopCat.mono_iff_injective (topologicalConeBaseIncl A)).mp inferInstance
  change hpo.cocone.inl p = hpo.cocone.inl q at h
  rcases (pushoutCocone_inl_eq_inl_iff_of_isColimit hpo.isColimit hb p q).mp h with
    hpq | ⟨a, b, hab, hpa, hqb⟩
  · exact hpq
  · have hpa' : p = topologicalConeBaseIncl A a := by
      simpa using hpa
    have hz : topologicalMappingConeHeightReal f
        (topologicalMappingConeConeIncl f p) = 0 := by
      rw [hpa']
      unfold topologicalMappingConeHeightReal
      rw [show topologicalMappingConeHeight f
          (topologicalMappingConeConeIncl f (topologicalConeBaseIncl A a)) =
          topologicalConeHeight A (topologicalConeBaseIncl A a) from
        ConcreteCategory.congr_hom (topologicalMappingConeConeIncl_height f) _]
      rw [show topologicalConeHeight A (topologicalConeBaseIncl A a) = 0 from
        ConcreteCategory.congr_hom (topologicalConeBaseIncl_height A) a]
      simp
    linarith

/-- The open lower collar, consisting of points of height less than `2/3`. -/
def mappingConeLower (f : A ⟶ X) : Set (topologicalMappingCone f) :=
  {p | topologicalMappingConeHeightReal f p < 2 / 3}

/-- The open upper collar, consisting of points of height greater than `1/3`. -/
def mappingConeUpper (f : A ⟶ X) : Set (topologicalMappingCone f) :=
  {p | 1 / 3 < topologicalMappingConeHeightReal f p}

theorem isOpen_mappingConeLower (f : A ⟶ X) : IsOpen (mappingConeLower f) :=
  isOpen_lt (continuous_topologicalMappingConeHeightReal f) continuous_const

theorem isOpen_mappingConeUpper (f : A ⟶ X) : IsOpen (mappingConeUpper f) :=
  isOpen_lt continuous_const (continuous_topologicalMappingConeHeightReal f)

/-- The upper and lower collars cover the mapping cone. -/
theorem mappingConeUpper_union_lower (f : A ⟶ X) :
    mappingConeUpper f ∪ mappingConeLower f = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro p
  change 1 / 3 < topologicalMappingConeHeightReal f p ∨
    topologicalMappingConeHeightReal f p < 2 / 3
  by_cases hp : topologicalMappingConeHeightReal f p ≤ 1 / 3
  · right
    linarith
  · left
    linarith

/-- Before passing to the mapping-cone quotient, collapse every cylinder line in the lower
collar to its attaching point.  The arbitrary value at the cone point is harmless because the
cone point is not in the preimage of the lower collar. -/
noncomputable def mappingConeLowerRaw (f : A ⟶ X) [Nonempty X] :
    C((X : Type u) ⊕ ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u} : TopCat.{u})), X) where
  toFun
    | Sum.inl x => x
    | Sum.inr (Sum.inl c) => f (fst A TopCat.I c)
    | Sum.inr (Sum.inr _) => Classical.choice inferInstance
  continuous_toFun := by
    rw [continuous_sum_dom]
    constructor
    · change Continuous (id : X → X)
      exact continuous_id
    · rw [continuous_sum_dom]
      constructor
      · exact (fst A TopCat.I ≫ f).hom.continuous
      · exact continuous_const

theorem topologicalMappingConeTripleDesc_point_not_mem_lower
    (f : A ⟶ X) (z : (𝟙_ TopCat.{u} : TopCat.{u})) :
    topologicalMappingConeTripleDesc f (Sum.inr (Sum.inr z)) ∉ mappingConeLower f := by
  change ¬ topologicalMappingConeHeightReal f
      (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inr z))) < 2 / 3
  simp
  norm_num

/-- The raw lower-collar retraction is constant on every fibre of the restricted mapping-cone
quotient. -/
theorem mappingConeLowerRaw_factors (f : A ⟶ X) [Nonempty X] :
    Function.FactorsThrough
      ((mappingConeLowerRaw f).restrict
        (topologicalMappingConeTripleDesc f ⁻¹' mappingConeLower f))
      ((mappingConeLower f).restrictPreimage (topologicalMappingConeTripleDesc f)) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
  have hpq' : topologicalMappingConeTripleDesc f p =
      topologicalMappingConeTripleDesc f q := congrArg Subtype.val hpq
  rcases p with x | (c | z)
  · rcases q with y | (d | w)
    · change x = y
      apply (TopCat.mono_iff_injective (topologicalMappingConeIncl f)).mp inferInstance
      exact hpq'
    · change x = f d.1
      apply topologicalMappingConeIncl_eq_cylinder_below f x d
      · change topologicalMappingConeHeightReal f
          (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl d))) < 2 / 3 at hq
        simpa only [topologicalMappingConeTripleDesc_cylinder_heightReal] using hq
      · exact hpq'
    · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f w hq).elim
  · rcases q with y | (d | w)
    · change f c.1 = y
      symm
      apply topologicalMappingConeIncl_eq_cylinder_below f y c
      · change topologicalMappingConeHeightReal f
          (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))) < 2 / 3 at hp
        simpa only [topologicalMappingConeTripleDesc_cylinder_heightReal] using hp
      · exact hpq'.symm
    · change f c.1 = f d.1
      apply topologicalMappingConeCylinder_eq_below f c d
      · change topologicalMappingConeHeightReal f
          (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))) < 2 / 3 at hp
        simpa only [topologicalMappingConeTripleDesc_cylinder_heightReal] using hp
      · change topologicalMappingConeHeightReal f
          (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl d))) < 2 / 3 at hq
        simpa only [topologicalMappingConeTripleDesc_cylinder_heightReal] using hq
      · exact hpq'
    · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f w hq).elim
  · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f z hp).elim

/-- The quotient map onto the lower mapping-cone collar. -/
def mappingConeLowerQuotient (f : A ⟶ X) : C(
    (topologicalMappingConeTripleDesc f ⁻¹' mappingConeLower f),
    mappingConeLower f) :=
  ⟨(mappingConeLower f).restrictPreimage (topologicalMappingConeTripleDesc f),
    ((topologicalMappingConeTripleDesc_isQuotientMap f).restrictPreimage_isOpen
      (isOpen_mappingConeLower f)).continuous⟩

theorem mappingConeLowerQuotient_isQuotientMap (f : A ⟶ X) :
    IsQuotientMap (mappingConeLowerQuotient f) :=
  (topologicalMappingConeTripleDesc_isQuotientMap f).restrictPreimage_isOpen
    (isOpen_mappingConeLower f)

/-- Retraction of the lower mapping-cone collar onto the original space. -/
noncomputable def mappingConeLowerRetract (f : A ⟶ X) [Nonempty X] :
    TopCat.of (mappingConeLower f) ⟶ X :=
  TopCat.ofHom ((mappingConeLowerQuotient_isQuotientMap f).lift
    ((mappingConeLowerRaw f).restrict
      (topologicalMappingConeTripleDesc f ⁻¹' mappingConeLower f))
    (mappingConeLowerRaw_factors f))

@[simp]
theorem mappingConeLowerRetract_quotient (f : A ⟶ X) [Nonempty X]
    (p : topologicalMappingConeTripleDesc f ⁻¹' mappingConeLower f) :
    mappingConeLowerRetract f (mappingConeLowerQuotient f p) = mappingConeLowerRaw f p := by
  exact ContinuousMap.congr_fun ((mappingConeLowerQuotient_isQuotientMap f).lift_comp
    ((mappingConeLowerRaw f).restrict
      (topologicalMappingConeTripleDesc f ⁻¹' mappingConeLower f))
    (mappingConeLowerRaw_factors f)) p

/-- Inclusion of the original space into the lower mapping-cone collar. -/
noncomputable def mappingConeLowerIncl (f : A ⟶ X) :
    X ⟶ TopCat.of (mappingConeLower f) := by
  apply TopCat.ofHom
  refine ⟨fun x ↦ ⟨topologicalMappingConeIncl f x, ?_⟩, ?_⟩
  · change topologicalMappingConeHeightReal f (topologicalMappingConeIncl f x) < 2 / 3
    unfold topologicalMappingConeHeightReal
    rw [show topologicalMappingConeHeight f (topologicalMappingConeIncl f x) = 0 from
      ConcreteCategory.congr_hom (topologicalMappingConeIncl_height f) x]
    norm_num
  · apply Continuous.subtype_mk (topologicalMappingConeIncl f).hom.continuous

@[simp]
theorem mappingConeLowerRetract_incl (f : A ⟶ X) [Nonempty X] (x : X) :
    mappingConeLowerRetract f (mappingConeLowerIncl f x) = x := by
  let p : topologicalMappingConeTripleDesc f ⁻¹' mappingConeLower f :=
    ⟨Sum.inl x, by
      change topologicalMappingConeHeightReal f
        (topologicalMappingConeTripleDesc f (Sum.inl x)) < 2 / 3
      simp⟩
  exact mappingConeLowerRetract_quotient f p

/-- The continuous formula underlying the lower-collar deformation.  At time `t`, it replaces a
cylinder height `s` by `min s t`. -/
noncomputable def mappingConeLowerDeformAmbientRaw (f : A ⟶ X) [Nonempty X] :
    C(unitInterval ×
      ((X : Type u) ⊕ ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u} : TopCat.{u}))),
      topologicalMappingCone f) where
  toFun p := match p.2 with
    | Sum.inl x => topologicalMappingConeIncl f x
    | Sum.inr (Sum.inl c) => topologicalMappingConeConeIncl f
        (topologicalConeCylinderIncl A
          (fst A TopCat.I c, TopCat.I.min (snd A TopCat.I c,
            TopCat.I.homeomorph.symm p.1)))
    | Sum.inr (Sum.inr _) =>
        topologicalMappingConeIncl f (Classical.choice inferInstance)
  continuous_toFun := by
    let L : (unitInterval × (A ⊗ TopCat.I : TopCat.{u})) ⊕
        (unitInterval × (𝟙_ TopCat.{u} : TopCat.{u})) → topologicalMappingCone f :=
      Sum.elim
        (fun p ↦ topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A
            (fst A TopCat.I p.2, TopCat.I.min (snd A TopCat.I p.2,
              TopCat.I.homeomorph.symm p.1))))
        (fun _ ↦ topologicalMappingConeIncl f (Classical.choice inferInstance))
    have hL : Continuous L := by
      rw [continuous_sum_dom]
      constructor <;> dsimp [L] <;> fun_prop
    have hright : Continuous (fun p : unitInterval ×
        ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u} : TopCat.{u})) ↦
        match p.2 with
        | Sum.inl c => topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A
              (fst A TopCat.I c, TopCat.I.min (snd A TopCat.I c,
                TopCat.I.homeomorph.symm p.1)))
        | Sum.inr _ =>
            topologicalMappingConeIncl f (Classical.choice inferInstance)) := by
      have hcomp := hL.comp (Homeomorph.prodSumDistrib :
        unitInterval × ((A ⊗ TopCat.I : TopCat.{u}) ⊕
          (𝟙_ TopCat.{u} : TopCat.{u})) ≃ₜ _).continuous
      convert hcomp using 1
      funext p
      rcases p with ⟨t, c | z⟩ <;> rfl
    let K : (unitInterval × (X : Type u)) ⊕
        (unitInterval × ((A ⊗ TopCat.I : TopCat.{u}) ⊕
          (𝟙_ TopCat.{u} : TopCat.{u}))) → topologicalMappingCone f :=
      Sum.elim (fun p ↦ topologicalMappingConeIncl f p.2)
        (fun p ↦ match p.2 with
          | Sum.inl c => topologicalMappingConeConeIncl f
              (topologicalConeCylinderIncl A
                (fst A TopCat.I c, TopCat.I.min (snd A TopCat.I c,
                  TopCat.I.homeomorph.symm p.1)))
          | Sum.inr _ =>
              topologicalMappingConeIncl f (Classical.choice inferInstance))
    have hK : Continuous K := by
      rw [continuous_sum_dom]
      exact ⟨by dsimp [K]; fun_prop, by simpa [K] using hright⟩
    have hcomp := hK.comp (Homeomorph.prodSumDistrib :
      unitInterval × ((X : Type u) ⊕ ((A ⊗ TopCat.I : TopCat.{u}) ⊕
        (𝟙_ TopCat.{u} : TopCat.{u}))) ≃ₜ _).continuous
    convert hcomp using 1
    funext p
    rcases p with ⟨t, x | r⟩
    · change _ = K (Homeomorph.prodSumDistrib (t, Sum.inl x))
      rw [show (Homeomorph.prodSumDistrib (t, Sum.inl x) :
        (unitInterval × (X : Type u)) ⊕ _) = Sum.inl (t, x) from rfl]
      rfl
    · change _ = K (Homeomorph.prodSumDistrib (t, Sum.inr r))
      rw [show (Homeomorph.prodSumDistrib (t, Sum.inr r) :
        (unitInterval × (X : Type u)) ⊕ _) = Sum.inr (t, r) from rfl]
      rcases r with c | z <;> rfl

@[simp]
theorem mappingConeLowerDeformAmbientRaw_inl
    (f : A ⟶ X) [Nonempty X] (t : unitInterval) (x : X) :
    mappingConeLowerDeformAmbientRaw f (t, Sum.inl x) =
      topologicalMappingConeIncl f x := rfl

@[simp]
theorem mappingConeLowerDeformAmbientRaw_cylinder
    (f : A ⟶ X) [Nonempty X] (t : unitInterval)
    (c : (A ⊗ TopCat.I : TopCat.{u})) :
    mappingConeLowerDeformAmbientRaw f (t, Sum.inr (Sum.inl c)) =
      topologicalMappingConeConeIncl f
        (topologicalConeCylinderIncl A (c.1, TopCat.I.min (c.2,
          TopCat.I.homeomorph.symm t))) := rfl

@[simp]
theorem mappingConeLowerDeformAmbientRaw_point
    (f : A ⟶ X) [Nonempty X] (t : unitInterval)
    (z : (𝟙_ TopCat.{u} : TopCat.{u})) :
    mappingConeLowerDeformAmbientRaw f (t, Sum.inr (Sum.inr z)) =
      topologicalMappingConeIncl f (Classical.choice inferInstance) := rfl

/-- The raw lower-collar deformation, restricted to the source of the lower quotient and bundled
with the proof that lowering height stays in the collar. -/
noncomputable def mappingConeLowerDeformRaw (f : A ⟶ X) [Nonempty X] :
    C(unitInterval ×
      (topologicalMappingConeTripleDesc f ⁻¹' mappingConeLower f),
      mappingConeLower f) where
  toFun p := ⟨mappingConeLowerDeformAmbientRaw f (p.1, p.2.1), by
    rcases p.2 with ⟨s, hs⟩
    rcases s with x | (c | z)
    · rw [mappingConeLowerDeformAmbientRaw_inl]
      change topologicalMappingConeHeightReal f (topologicalMappingConeIncl f x) < 2 / 3
      unfold topologicalMappingConeHeightReal
      rw [show topologicalMappingConeHeight f (topologicalMappingConeIncl f x) = 0 from
        ConcreteCategory.congr_hom (topologicalMappingConeIncl_height f) x]
      norm_num
    · rw [mappingConeLowerDeformAmbientRaw_cylinder]
      change topologicalMappingConeHeightReal f
        (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A
          (c.1, TopCat.I.min (c.2, TopCat.I.homeomorph.symm p.1)))) < 2 / 3
      unfold topologicalMappingConeHeightReal
      rw [show topologicalMappingConeHeight f
          (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A
            (c.1, TopCat.I.min (c.2, TopCat.I.homeomorph.symm p.1)))) =
          topologicalConeHeight A (topologicalConeCylinderIncl A
            (c.1, TopCat.I.min (c.2, TopCat.I.homeomorph.symm p.1))) from
        ConcreteCategory.congr_hom (topologicalMappingConeConeIncl_height f) _]
      rw [show topologicalConeHeight A (topologicalConeCylinderIncl A
          (c.1, TopCat.I.min (c.2, TopCat.I.homeomorph.symm p.1))) =
          TopCat.I.min (c.2, TopCat.I.homeomorph.symm p.1) from
        ConcreteCategory.congr_hom (topologicalConeCylinderIncl_height A) _]
      rw [TopCat.I.min_apply]
      apply lt_of_le_of_lt (min_le_left _ _)
      change topologicalMappingConeHeightReal f
        (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))) < 2 / 3 at hs
      simpa only [topologicalMappingConeTripleDesc_cylinder_heightReal] using hs
    · rw [mappingConeLowerDeformAmbientRaw_point]
      change topologicalMappingConeHeightReal f
        (topologicalMappingConeIncl f (Classical.choice inferInstance)) < 2 / 3
      unfold topologicalMappingConeHeightReal
      rw [show topologicalMappingConeHeight f
          (topologicalMappingConeIncl f (Classical.choice inferInstance)) = 0 from
        ConcreteCategory.congr_hom (topologicalMappingConeIncl_height f) _]
      norm_num⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (mappingConeLowerDeformAmbientRaw f).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- At every time, the lower-collar deformation is constant on fibres of the restricted
mapping-cone quotient. -/
theorem mappingConeLowerDeformRaw_factors
    (f : A ⟶ X) [Nonempty X] (t : unitInterval) :
    Function.FactorsThrough
      (fun p : topologicalMappingConeTripleDesc f ⁻¹' mappingConeLower f ↦
        mappingConeLowerDeformRaw f (t, p))
      (mappingConeLowerQuotient f) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
  have hpq' : topologicalMappingConeTripleDesc f p =
      topologicalMappingConeTripleDesc f q := congrArg Subtype.val hpq
  apply SetCoe.ext
  rcases p with x | (c | z)
  · rcases q with y | (d | w)
    · change topologicalMappingConeIncl f x = topologicalMappingConeIncl f y
      congr 1
      apply (TopCat.mono_iff_injective (topologicalMappingConeIncl f)).mp inferInstance
      exact hpq'
    · change topologicalMappingConeIncl f x = topologicalMappingConeConeIncl f
        (topologicalConeCylinderIncl A (d.1,
          TopCat.I.min (d.2, TopCat.I.homeomorph.symm t)))
      exact topologicalMappingConeIncl_eq_scaledCylinder f x d
        (TopCat.I.homeomorph.symm t) hpq'
    · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f w hq).elim
  · rcases q with y | (d | w)
    · change topologicalMappingConeConeIncl f
        (topologicalConeCylinderIncl A (c.1,
          TopCat.I.min (c.2, TopCat.I.homeomorph.symm t))) =
        topologicalMappingConeIncl f y
      exact (topologicalMappingConeIncl_eq_scaledCylinder f y c
        (TopCat.I.homeomorph.symm t) hpq'.symm).symm
    · change topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A (c.1,
            TopCat.I.min (c.2, TopCat.I.homeomorph.symm t))) =
        topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A (d.1,
            TopCat.I.min (d.2, TopCat.I.homeomorph.symm t)))
      apply topologicalMappingConeScaledCylinder_eq f c d
      · change topologicalMappingConeHeightReal f
          (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))) < 2 / 3 at hp
        simpa only [topologicalMappingConeTripleDesc_cylinder_heightReal] using hp
      · change topologicalMappingConeHeightReal f
          (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl d))) < 2 / 3 at hq
        simpa only [topologicalMappingConeTripleDesc_cylinder_heightReal] using hq
      · exact hpq'
    · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f w hq).elim
  · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f z hp).elim

/-- The raw deformation at a fixed time. -/
def mappingConeLowerDeformRawAt
    (f : A ⟶ X) [Nonempty X] (t : unitInterval) :
    C(topologicalMappingConeTripleDesc f ⁻¹' mappingConeLower f,
      mappingConeLower f) where
  toFun p := mappingConeLowerDeformRaw f (t, p)
  continuous_toFun := (mappingConeLowerDeformRaw f).continuous.comp
    (continuous_const.prodMk continuous_id)

/-- The descended lower-collar deformation at a fixed time. -/
noncomputable def mappingConeLowerDeformAt
    (f : A ⟶ X) [Nonempty X] (t : unitInterval) :
    TopCat.of (mappingConeLower f) ⟶ TopCat.of (mappingConeLower f) :=
  TopCat.ofHom ((mappingConeLowerQuotient_isQuotientMap f).lift
    (mappingConeLowerDeformRawAt f t) (mappingConeLowerDeformRaw_factors f t))

@[simp]
theorem mappingConeLowerDeformAt_quotient
    (f : A ⟶ X) [Nonempty X] (t : unitInterval)
    (p : topologicalMappingConeTripleDesc f ⁻¹' mappingConeLower f) :
    mappingConeLowerDeformAt f t (mappingConeLowerQuotient f p) =
      mappingConeLowerDeformRaw f (t, p) := by
  exact ContinuousMap.congr_fun ((mappingConeLowerQuotient_isQuotientMap f).lift_comp
    (mappingConeLowerDeformRawAt f t) (mappingConeLowerDeformRaw_factors f t)) p

theorem continuous_mappingConeLowerDeformAt (f : A ⟶ X) [Nonempty X] :
    Continuous (fun p : unitInterval × mappingConeLower f ↦
      mappingConeLowerDeformAt f p.1 p.2) := by
  apply (mappingConeLowerQuotient_isQuotientMap f).continuous_lift_prod_right
  convert (mappingConeLowerDeformRaw f).continuous using 1
  funext p
  rw [mappingConeLowerDeformAt_quotient]

theorem mappingConeLowerDeformAt_zero
    (f : A ⟶ X) [Nonempty X] (z : mappingConeLower f) :
    mappingConeLowerDeformAt f 0 z =
      (mappingConeLowerRetract f ≫ mappingConeLowerIncl f) z := by
  obtain ⟨p, rfl⟩ := (mappingConeLowerQuotient_isQuotientMap f).surjective z
  rw [mappingConeLowerDeformAt_quotient]
  rcases p with ⟨s, hs⟩
  rcases s with x | (c | w)
  · change mappingConeLowerDeformRaw f (0, ⟨Sum.inl x, hs⟩) =
      mappingConeLowerIncl f
        (mappingConeLowerRetract f (mappingConeLowerQuotient f ⟨Sum.inl x, hs⟩))
    rw [mappingConeLowerRetract_quotient]
    apply SetCoe.ext
    rfl
  · change mappingConeLowerDeformRaw f (0, ⟨Sum.inr (Sum.inl c), hs⟩) =
      mappingConeLowerIncl f
        (mappingConeLowerRetract f
          (mappingConeLowerQuotient f ⟨Sum.inr (Sum.inl c), hs⟩))
    rw [mappingConeLowerRetract_quotient]
    apply SetCoe.ext
    change topologicalMappingConeConeIncl f
        (topologicalConeCylinderIncl A (c.1,
          TopCat.I.min (c.2, TopCat.I.homeomorph.symm 0))) =
      topologicalMappingConeIncl f (f c.1)
    rw [show TopCat.I.homeomorph.symm (0 : unitInterval) = 0 by rfl,
      TopCat.I.min_zero_right]
    exact (ConcreteCategory.congr_hom (topologicalMappingCone_condition f) c.1).symm
  · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f w hs).elim

theorem mappingConeLowerDeformAt_one
    (f : A ⟶ X) [Nonempty X] (z : mappingConeLower f) :
    mappingConeLowerDeformAt f 1 z = z := by
  obtain ⟨p, rfl⟩ := (mappingConeLowerQuotient_isQuotientMap f).surjective z
  rw [mappingConeLowerDeformAt_quotient]
  rcases p with ⟨s, hs⟩
  rcases s with x | (c | w)
  · apply SetCoe.ext
    rfl
  · apply SetCoe.ext
    change topologicalMappingConeConeIncl f
        (topologicalConeCylinderIncl A (c.1,
          TopCat.I.min (c.2, TopCat.I.homeomorph.symm 1))) =
      topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))
    rw [show TopCat.I.homeomorph.symm (1 : unitInterval) = 1 by rfl,
      TopCat.I.min_one_right]
    rfl
  · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f w hs).elim

/-- Strong deformation of the lower collar onto the original mapping-cone summand. -/
noncomputable def mappingConeLowerDeformation (f : A ⟶ X) [Nonempty X] :
    TopCat.Homotopy (mappingConeLowerRetract f ≫ mappingConeLowerIncl f)
      (𝟙 (TopCat.of (mappingConeLower f))) where
  toFun p := mappingConeLowerDeformAt f p.1 p.2
  continuous_toFun := continuous_mappingConeLowerDeformAt f
  map_zero_left z := mappingConeLowerDeformAt_zero f z
  map_one_left z := mappingConeLowerDeformAt_one f z

/-- The lower mapping-cone collar is homotopy equivalent to the original space. -/
noncomputable def mappingConeLowerHomotopyEquiv (f : A ⟶ X) [Nonempty X] :
    ContinuousMap.HomotopyEquiv (mappingConeLower f) X where
  toFun := (mappingConeLowerRetract f).hom
  invFun := (mappingConeLowerIncl f).hom
  left_inv := ⟨mappingConeLowerDeformation f⟩
  right_inv := by
    have h : mappingConeLowerIncl f ≫ mappingConeLowerRetract f = 𝟙 X := by
      ext x
      exact mappingConeLowerRetract_incl f x
    rw [← TopCat.hom_comp, h, TopCat.hom_id]

/-- The distinguished apex of a topological cone. -/
def topologicalConeApex (A : TopCat.{u}) : topologicalCone A :=
  topologicalConePointIncl A
    (SemiCartesianMonoidalCategory.isTerminalTensorUnit.from
      (TopCat.of PUnit.{u + 1}) PUnit.unit)

/-- The apex, regarded as a point of the upper mapping-cone collar. -/
def mappingConeUpperApex (f : A ⟶ X) : mappingConeUpper f :=
  ⟨topologicalMappingConeConeIncl f (topologicalConeApex A), by
    change 1 / 3 < topologicalMappingConeHeightReal f
      (topologicalMappingConeConeIncl f (topologicalConePointIncl A _))
    unfold topologicalMappingConeHeightReal
    rw [show topologicalMappingConeHeight f
        (topologicalMappingConeConeIncl f (topologicalConePointIncl A _)) =
        topologicalConeHeight A (topologicalConePointIncl A _) from
      ConcreteCategory.congr_hom (topologicalMappingConeConeIncl_height f) _]
    rw [show topologicalConeHeight A (topologicalConePointIncl A _) = 1 from
      ConcreteCategory.congr_hom (topologicalConePointIncl_height A) _]
    simp
    norm_num⟩

/-- The quotient map onto the upper mapping-cone collar. -/
def mappingConeUpperQuotient (f : A ⟶ X) : C(
    (topologicalMappingConeTripleDesc f ⁻¹' mappingConeUpper f),
    mappingConeUpper f) :=
  ⟨(mappingConeUpper f).restrictPreimage (topologicalMappingConeTripleDesc f),
    ((topologicalMappingConeTripleDesc_isQuotientMap f).restrictPreimage_isOpen
      (isOpen_mappingConeUpper f)).continuous⟩

theorem mappingConeUpperQuotient_isQuotientMap (f : A ⟶ X) :
    IsQuotientMap (mappingConeUpperQuotient f) :=
  (topologicalMappingConeTripleDesc_isQuotientMap f).restrictPreimage_isOpen
    (isOpen_mappingConeUpper f)

/-- The cone quotient bundled as a continuous map. -/
def topologicalConeSumDescMap (A : TopCat.{u}) :
    C((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u} : TopCat.{u}),
      topologicalCone A) :=
  ⟨topologicalConeSumDesc A, (topologicalConeSumDesc_isQuotientMap A).continuous⟩

/-- Raise the cone coordinate on the cone part of the three-piece presentation. -/
def mappingConeUpperConeRawDeform (f : A ⟶ X) :
    C(unitInterval ×
      ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u} : TopCat.{u})),
      topologicalMappingCone f) :=
  (topologicalMappingConeConeIncl f).hom.comp
    ((topologicalConeContractHomotopy A).toContinuousMap.comp
      (ContinuousMap.prodMap (ContinuousMap.id unitInterval)
        (topologicalConeSumDescMap A)))

/-- The continuous formula underlying contraction of the upper collar to the cone apex. -/
noncomputable def mappingConeUpperDeformAmbientRaw (f : A ⟶ X) :
    C(unitInterval ×
      ((X : Type u) ⊕ ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u} : TopCat.{u}))),
      topologicalMappingCone f) := by
  let S : Type u := (X : Type u) ⊕
    ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u} : TopCat.{u}))
  let R : Type u := (A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u} : TopCat.{u})
  let K : C((unitInterval × (X : Type u)) ⊕ (unitInterval × R),
      topologicalMappingCone f) :=
    ⟨Sum.elim (fun _ ↦ topologicalMappingConeConeIncl f (topologicalConeApex A))
      (mappingConeUpperConeRawDeform f), by
        rw [continuous_sum_dom]
        exact ⟨continuous_const, (mappingConeUpperConeRawDeform f).continuous⟩⟩
  let e : C(unitInterval × S,
      (unitInterval × (X : Type u)) ⊕ (unitInterval × R)) :=
    ⟨Homeomorph.prodSumDistrib, Homeomorph.prodSumDistrib.continuous⟩
  exact K.comp e

@[simp]
theorem mappingConeUpperDeformAmbientRaw_inl
    (f : A ⟶ X) (t : unitInterval) (x : X) :
    mappingConeUpperDeformAmbientRaw f (t, Sum.inl x) =
      topologicalMappingConeConeIncl f (topologicalConeApex A) := rfl

@[simp]
theorem mappingConeUpperDeformAmbientRaw_inr
    (f : A ⟶ X) (t : unitInterval)
    (q : (A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u} : TopCat.{u})) :
    mappingConeUpperDeformAmbientRaw f (t, Sum.inr q) =
      topologicalMappingConeConeIncl f
        (topologicalConeContractAt A (TopCat.I.homeomorph.symm t)
          (topologicalConeSumDesc A q)) := rfl

/-- The upper-collar contraction formula, restricted and bundled with the fact that raising
height stays in the upper collar. -/
noncomputable def mappingConeUpperDeformRaw (f : A ⟶ X) :
    C(unitInterval ×
      (topologicalMappingConeTripleDesc f ⁻¹' mappingConeUpper f),
      mappingConeUpper f) where
  toFun p := ⟨mappingConeUpperDeformAmbientRaw f (p.1, p.2.1), by
    rcases p.2 with ⟨s, hs⟩
    rcases s with x | (c | z)
    · rw [mappingConeUpperDeformAmbientRaw_inl]
      exact (mappingConeUpperApex f).property
    · rw [mappingConeUpperDeformAmbientRaw_inr]
      change 1 / 3 < topologicalMappingConeHeightReal f
        (topologicalMappingConeConeIncl f
          (topologicalConeContractAt A (TopCat.I.homeomorph.symm p.1)
            (topologicalConeCylinderIncl A c)))
      rw [show topologicalConeContractAt A (TopCat.I.homeomorph.symm p.1)
          (topologicalConeCylinderIncl A c) =
          topologicalConeCylinderIncl A
            (c.1, TopCat.I.max (c.2, TopCat.I.homeomorph.symm p.1)) from
        ConcreteCategory.congr_hom
          (topologicalConeCylinderIncl_contractAt A (TopCat.I.homeomorph.symm p.1)) c]
      unfold topologicalMappingConeHeightReal
      rw [show topologicalMappingConeHeight f
          (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A
            (c.1, TopCat.I.max (c.2, TopCat.I.homeomorph.symm p.1)))) =
          topologicalConeHeight A (topologicalConeCylinderIncl A
            (c.1, TopCat.I.max (c.2, TopCat.I.homeomorph.symm p.1))) from
        ConcreteCategory.congr_hom (topologicalMappingConeConeIncl_height f) _]
      rw [show topologicalConeHeight A (topologicalConeCylinderIncl A
          (c.1, TopCat.I.max (c.2, TopCat.I.homeomorph.symm p.1))) =
          TopCat.I.max (c.2, TopCat.I.homeomorph.symm p.1) from
        ConcreteCategory.congr_hom (topologicalConeCylinderIncl_height A) _]
      rw [TopCat.I.max_apply]
      apply lt_of_lt_of_le _ (le_max_left _ _)
      change 1 / 3 < topologicalMappingConeHeightReal f
        (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))) at hs
      simpa only [topologicalMappingConeTripleDesc_cylinder_heightReal] using hs
    · rw [mappingConeUpperDeformAmbientRaw_inr]
      change 1 / 3 < topologicalMappingConeHeightReal f
        (topologicalMappingConeConeIncl f
          (topologicalConeContractAt A (TopCat.I.homeomorph.symm p.1)
            (topologicalConePointIncl A z)))
      rw [show topologicalConeContractAt A (TopCat.I.homeomorph.symm p.1)
          (topologicalConePointIncl A z) = topologicalConePointIncl A z from
        ConcreteCategory.congr_hom
          (topologicalConePointIncl_contractAt A (TopCat.I.homeomorph.symm p.1)) z]
      unfold topologicalMappingConeHeightReal
      rw [show topologicalMappingConeHeight f
          (topologicalMappingConeConeIncl f (topologicalConePointIncl A z)) =
          topologicalConeHeight A (topologicalConePointIncl A z) from
        ConcreteCategory.congr_hom (topologicalMappingConeConeIncl_height f) _]
      rw [show topologicalConeHeight A (topologicalConePointIncl A z) = 1 from
        ConcreteCategory.congr_hom (topologicalConePointIncl_height A) z]
      simp
      norm_num⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (mappingConeUpperDeformAmbientRaw f).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

theorem topologicalMappingConeTripleDesc_inl_not_mem_upper
    (f : A ⟶ X) (x : X) :
    topologicalMappingConeTripleDesc f (Sum.inl x) ∉ mappingConeUpper f := by
  change ¬ 1 / 3 < topologicalMappingConeHeightReal f
    (topologicalMappingConeTripleDesc f (Sum.inl x))
  simp

/-- At every time, the upper-collar contraction is constant on fibres of the restricted
mapping-cone quotient. -/
theorem mappingConeUpperDeformRaw_factors
    (f : A ⟶ X) (t : unitInterval) :
    Function.FactorsThrough
      (fun p : topologicalMappingConeTripleDesc f ⁻¹' mappingConeUpper f ↦
        mappingConeUpperDeformRaw f (t, p))
      (mappingConeUpperQuotient f) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
  have hpq' : topologicalMappingConeTripleDesc f p =
      topologicalMappingConeTripleDesc f q := congrArg Subtype.val hpq
  rcases p with x | r
  · exact (topologicalMappingConeTripleDesc_inl_not_mem_upper f x hp).elim
  · rcases q with y | s
    · exact (topologicalMappingConeTripleDesc_inl_not_mem_upper f y hq).elim
    · apply SetCoe.ext
      change topologicalMappingConeConeIncl f
          (topologicalConeContractAt A (TopCat.I.homeomorph.symm t)
            (topologicalConeSumDesc A r)) =
        topologicalMappingConeConeIncl f
          (topologicalConeContractAt A (TopCat.I.homeomorph.symm t)
            (topologicalConeSumDesc A s))
      congr 1
      apply congrArg (topologicalConeContractAt A (TopCat.I.homeomorph.symm t))
      apply topologicalMappingConeConeIncl_eq_of_height_pos f
      · change 1 / 3 < topologicalMappingConeHeightReal f
          (topologicalMappingConeTripleDesc f (Sum.inr r)) at hp
        change 1 / 3 < topologicalMappingConeHeightReal f
          (topologicalMappingConeConeIncl f (topologicalConeSumDesc A r)) at hp
        linarith
      · exact hpq'

/-- The raw upper-collar contraction at a fixed time. -/
def mappingConeUpperDeformRawAt (f : A ⟶ X) (t : unitInterval) :
    C(topologicalMappingConeTripleDesc f ⁻¹' mappingConeUpper f,
      mappingConeUpper f) where
  toFun p := mappingConeUpperDeformRaw f (t, p)
  continuous_toFun := (mappingConeUpperDeformRaw f).continuous.comp
    (continuous_const.prodMk continuous_id)

/-- The descended upper-collar contraction at a fixed time. -/
noncomputable def mappingConeUpperDeformAt (f : A ⟶ X) (t : unitInterval) :
    TopCat.of (mappingConeUpper f) ⟶ TopCat.of (mappingConeUpper f) :=
  TopCat.ofHom ((mappingConeUpperQuotient_isQuotientMap f).lift
    (mappingConeUpperDeformRawAt f t) (mappingConeUpperDeformRaw_factors f t))

@[simp]
theorem mappingConeUpperDeformAt_quotient
    (f : A ⟶ X) (t : unitInterval)
    (p : topologicalMappingConeTripleDesc f ⁻¹' mappingConeUpper f) :
    mappingConeUpperDeformAt f t (mappingConeUpperQuotient f p) =
      mappingConeUpperDeformRaw f (t, p) := by
  exact ContinuousMap.congr_fun ((mappingConeUpperQuotient_isQuotientMap f).lift_comp
    (mappingConeUpperDeformRawAt f t) (mappingConeUpperDeformRaw_factors f t)) p

theorem continuous_mappingConeUpperDeformAt (f : A ⟶ X) :
    Continuous (fun p : unitInterval × mappingConeUpper f ↦
      mappingConeUpperDeformAt f p.1 p.2) := by
  apply (mappingConeUpperQuotient_isQuotientMap f).continuous_lift_prod_right
  convert (mappingConeUpperDeformRaw f).continuous using 1
  funext p
  rw [mappingConeUpperDeformAt_quotient]

theorem mappingConeUpperDeformAt_zero
    (f : A ⟶ X) (z : mappingConeUpper f) :
    mappingConeUpperDeformAt f 0 z = z := by
  obtain ⟨p, rfl⟩ := (mappingConeUpperQuotient_isQuotientMap f).surjective z
  rw [mappingConeUpperDeformAt_quotient]
  rcases p with ⟨s, hs⟩
  rcases s with x | q
  · exact (topologicalMappingConeTripleDesc_inl_not_mem_upper f x hs).elim
  · apply SetCoe.ext
    change topologicalMappingConeConeIncl f
        (topologicalConeContractAt A (TopCat.I.homeomorph.symm 0)
          (topologicalConeSumDesc A q)) =
      topologicalMappingConeTripleDesc f (Sum.inr q)
    rw [show TopCat.I.homeomorph.symm (0 : unitInterval) = 0 by rfl,
      topologicalConeContractAt_zero]
    rfl

theorem mappingConeUpperDeformAt_one
    (f : A ⟶ X) (z : mappingConeUpper f) :
    mappingConeUpperDeformAt f 1 z = mappingConeUpperApex f := by
  obtain ⟨p, rfl⟩ := (mappingConeUpperQuotient_isQuotientMap f).surjective z
  rw [mappingConeUpperDeformAt_quotient]
  rcases p with ⟨s, hs⟩
  rcases s with x | q
  · exact (topologicalMappingConeTripleDesc_inl_not_mem_upper f x hs).elim
  · apply SetCoe.ext
    change topologicalMappingConeConeIncl f
        (topologicalConeContractAt A (TopCat.I.homeomorph.symm 1)
          (topologicalConeSumDesc A q)) =
      topologicalMappingConeConeIncl f (topologicalConeApex A)
    rw [show TopCat.I.homeomorph.symm (1 : unitInterval) = 1 by rfl,
      topologicalConeContractAt_one]
    congr 2

/-- Contraction of the upper mapping-cone collar to its apex. -/
noncomputable def mappingConeUpperContraction (f : A ⟶ X) :
    TopCat.Homotopy (𝟙 (TopCat.of (mappingConeUpper f)))
      (TopCat.const (mappingConeUpperApex f)) where
  toFun p := mappingConeUpperDeformAt f p.1 p.2
  continuous_toFun := continuous_mappingConeUpperDeformAt f
  map_zero_left z := mappingConeUpperDeformAt_zero f z
  map_one_left z := mappingConeUpperDeformAt_one f z

theorem contractibleSpace_mappingConeUpper (f : A ⟶ X) :
    ContractibleSpace (mappingConeUpper f) :=
  (contractible_iff_id_nullhomotopic (mappingConeUpper f)).mpr
    ⟨mappingConeUpperApex f, ⟨mappingConeUpperContraction f⟩⟩

instance (f : A ⟶ X) : ContractibleSpace (mappingConeUpper f) :=
  contractibleSpace_mappingConeUpper f

/-- The middle collar, i.e. the overlap of the upper and lower mapping-cone collars. -/
def mappingConeMiddle (f : A ⟶ X) : Set (topologicalMappingCone f) :=
  mappingConeUpper f ∩ mappingConeLower f

theorem isOpen_mappingConeMiddle (f : A ⟶ X) : IsOpen (mappingConeMiddle f) :=
  (isOpen_mappingConeUpper f).inter (isOpen_mappingConeLower f)

/-- The quotient map onto the middle mapping-cone collar. -/
def mappingConeMiddleQuotient (f : A ⟶ X) : C(
    (topologicalMappingConeTripleDesc f ⁻¹' mappingConeMiddle f),
    mappingConeMiddle f) :=
  ⟨(mappingConeMiddle f).restrictPreimage (topologicalMappingConeTripleDesc f),
    ((topologicalMappingConeTripleDesc_isQuotientMap f).restrictPreimage_isOpen
      (isOpen_mappingConeMiddle f)).continuous⟩

theorem mappingConeMiddleQuotient_isQuotientMap (f : A ⟶ X) :
    IsQuotientMap (mappingConeMiddleQuotient f) :=
  (topologicalMappingConeTripleDesc_isQuotientMap f).restrictPreimage_isOpen
    (isOpen_mappingConeMiddle f)

/-- Projection of the three-piece presentation onto the attaching space.  Its values on the
original-space and cone-point branches are irrelevant because neither branch meets the middle
collar. -/
noncomputable def mappingConeMiddleRaw (_f : A ⟶ X) [Nonempty A] :
    C((X : Type u) ⊕ ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u} : TopCat.{u})), A) where
  toFun
    | Sum.inl _ => Classical.choice inferInstance
    | Sum.inr (Sum.inl c) => fst A TopCat.I c
    | Sum.inr (Sum.inr _) => Classical.choice inferInstance
  continuous_toFun := by
    rw [continuous_sum_dom]
    constructor
    · exact continuous_const
    · rw [continuous_sum_dom]
      exact ⟨(fst A TopCat.I).hom.continuous, continuous_const⟩

/-- The middle projection is constant on fibres of the restricted mapping-cone quotient. -/
theorem mappingConeMiddleRaw_factors (f : A ⟶ X) [Nonempty A] :
    Function.FactorsThrough
      ((mappingConeMiddleRaw f).restrict
        (topologicalMappingConeTripleDesc f ⁻¹' mappingConeMiddle f))
      (mappingConeMiddleQuotient f) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
  have hpq' : topologicalMappingConeTripleDesc f p =
      topologicalMappingConeTripleDesc f q := congrArg Subtype.val hpq
  change topologicalMappingConeTripleDesc f p ∈ mappingConeUpper f ∧
    topologicalMappingConeTripleDesc f p ∈ mappingConeLower f at hp
  change topologicalMappingConeTripleDesc f q ∈ mappingConeUpper f ∧
    topologicalMappingConeTripleDesc f q ∈ mappingConeLower f at hq
  rcases p with x | (c | z)
  · exact (topologicalMappingConeTripleDesc_inl_not_mem_upper f x hp.1).elim
  · rcases q with y | (d | w)
    · exact (topologicalMappingConeTripleDesc_inl_not_mem_upper f y hq.1).elim
    · change c.1 = d.1
      have hcone : topologicalConeCylinderIncl A c =
          topologicalConeCylinderIncl A d := by
        apply topologicalMappingConeConeIncl_eq_of_height_pos f
        · have hpU := hp.1
          change 1 / 3 < topologicalMappingConeHeightReal f
            (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))) at hpU
          change 1 / 3 < topologicalMappingConeHeightReal f
            (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c)) at hpU
          linarith
        · exact hpq'
      apply congrArg Prod.fst
      apply topologicalConeCylinderIncl_eq_iff_below c d
      · have hpL := hp.2
        change topologicalMappingConeHeightReal f
          (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))) < 2 / 3 at hpL
        simpa only [topologicalMappingConeTripleDesc_cylinder_heightReal] using hpL
      · exact hcone
    · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f w hq.2).elim
  · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f z hp.2).elim

/-- Retraction of the middle collar onto the attaching space. -/
noncomputable def mappingConeMiddleRetract (f : A ⟶ X) [Nonempty A] :
    TopCat.of (mappingConeMiddle f) ⟶ A :=
  TopCat.ofHom ((mappingConeMiddleQuotient_isQuotientMap f).lift
    ((mappingConeMiddleRaw f).restrict
      (topologicalMappingConeTripleDesc f ⁻¹' mappingConeMiddle f))
    (mappingConeMiddleRaw_factors f))

@[simp]
theorem mappingConeMiddleRetract_quotient
    (f : A ⟶ X) [Nonempty A]
    (p : topologicalMappingConeTripleDesc f ⁻¹' mappingConeMiddle f) :
    mappingConeMiddleRetract f (mappingConeMiddleQuotient f p) =
      mappingConeMiddleRaw f p := by
  exact ContinuousMap.congr_fun ((mappingConeMiddleQuotient_isQuotientMap f).lift_comp
    ((mappingConeMiddleRaw f).restrict
      (topologicalMappingConeTripleDesc f ⁻¹' mappingConeMiddle f))
    (mappingConeMiddleRaw_factors f)) p

/-- Midpoint inclusion of the attaching space into the middle collar. -/
noncomputable def mappingConeMiddleIncl (f : A ⟶ X) :
    A ⟶ TopCat.of (mappingConeMiddle f) := by
  apply TopCat.ofHom
  refine ⟨fun a ↦ ⟨topologicalMappingConeConeIncl f
    (topologicalConeCylinderIncl A (a, TopCat.I.midpoint.{u})), ?_⟩, ?_⟩
  · change 1 / 3 < topologicalMappingConeHeightReal f
        (topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A (a, TopCat.I.midpoint.{u}))) ∧
      topologicalMappingConeHeightReal f
        (topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A (a, TopCat.I.midpoint.{u}))) < 2 / 3
    unfold topologicalMappingConeHeightReal
    rw [show topologicalMappingConeHeight f
        (topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A (a, TopCat.I.midpoint.{u}))) =
        topologicalConeHeight A
          (topologicalConeCylinderIncl A (a, TopCat.I.midpoint.{u})) from
      ConcreteCategory.congr_hom (topologicalMappingConeConeIncl_height f) _]
    rw [show topologicalConeHeight A
        (topologicalConeCylinderIncl A (a, TopCat.I.midpoint.{u})) =
        TopCat.I.midpoint.{u} from
      ConcreteCategory.congr_hom (topologicalConeCylinderIncl_height A) _]
    simp [TopCat.I.midpoint]
    norm_num
  · apply Continuous.subtype_mk
    fun_prop

@[simp]
theorem mappingConeMiddleRetract_incl
    (f : A ⟶ X) [Nonempty A] (a : A) :
    mappingConeMiddleRetract f (mappingConeMiddleIncl f a) = a := by
  let p : topologicalMappingConeTripleDesc f ⁻¹' mappingConeMiddle f :=
    ⟨Sum.inr (Sum.inl (a, TopCat.I.midpoint.{u})), by
      exact (mappingConeMiddleIncl f a).property⟩
  exact mappingConeMiddleRetract_quotient f p

/-- The continuous interpolation formula underlying deformation of the middle collar to its
midpoint copy of the attaching space. -/
noncomputable def mappingConeMiddleDeformAmbientRaw
    (f : A ⟶ X) [Nonempty A] :
    C(unitInterval × ((X : Type u) ⊕
      ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u} : TopCat.{u}))),
      topologicalMappingCone f) where
  toFun p := match p.2 with
    | Sum.inl _ => (mappingConeMiddleIncl f (Classical.choice inferInstance)).1
    | Sum.inr (Sum.inl c) => topologicalMappingConeConeIncl f
        (topologicalConeCylinderIncl A
          (fst A TopCat.I c, TopCat.I.midpointLerp
            (snd A TopCat.I c, TopCat.I.homeomorph.symm p.1)))
    | Sum.inr (Sum.inr _) =>
        (mappingConeMiddleIncl f (Classical.choice inferInstance)).1
  continuous_toFun := by
    let L : (unitInterval × (A ⊗ TopCat.I : TopCat.{u})) ⊕
        (unitInterval × (𝟙_ TopCat.{u} : TopCat.{u})) → topologicalMappingCone f :=
      Sum.elim
        (fun p ↦ topologicalMappingConeConeIncl f
          (topologicalConeCylinderIncl A
            (fst A TopCat.I p.2, TopCat.I.midpointLerp
              (snd A TopCat.I p.2, TopCat.I.homeomorph.symm p.1))))
        (fun _ ↦ (mappingConeMiddleIncl f (Classical.choice inferInstance)).1)
    have hL : Continuous L := by
      rw [continuous_sum_dom]
      constructor <;> dsimp [L] <;> fun_prop
    have hright : Continuous (fun p : unitInterval ×
        ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u} : TopCat.{u})) ↦
        match p.2 with
        | Sum.inl c => topologicalMappingConeConeIncl f
            (topologicalConeCylinderIncl A
              (fst A TopCat.I c, TopCat.I.midpointLerp
                (snd A TopCat.I c, TopCat.I.homeomorph.symm p.1)))
        | Sum.inr _ =>
            (mappingConeMiddleIncl f (Classical.choice inferInstance)).1) := by
      have hcomp := hL.comp (Homeomorph.prodSumDistrib : unitInterval ×
        ((A ⊗ TopCat.I : TopCat.{u}) ⊕ (𝟙_ TopCat.{u} : TopCat.{u})) ≃ₜ _).continuous
      convert hcomp using 1
      funext p
      rcases p with ⟨t, c | z⟩ <;> rfl
    let K : (unitInterval × (X : Type u)) ⊕
        (unitInterval × ((A ⊗ TopCat.I : TopCat.{u}) ⊕
          (𝟙_ TopCat.{u} : TopCat.{u}))) → topologicalMappingCone f :=
      Sum.elim (fun _ ↦ (mappingConeMiddleIncl f (Classical.choice inferInstance)).1)
        (fun p ↦ match p.2 with
          | Sum.inl c => topologicalMappingConeConeIncl f
              (topologicalConeCylinderIncl A
                (fst A TopCat.I c, TopCat.I.midpointLerp
                  (snd A TopCat.I c, TopCat.I.homeomorph.symm p.1)))
          | Sum.inr _ =>
              (mappingConeMiddleIncl f (Classical.choice inferInstance)).1)
    have hK : Continuous K := by
      rw [continuous_sum_dom]
      exact ⟨continuous_const, by simpa [K] using hright⟩
    have hcomp := hK.comp (Homeomorph.prodSumDistrib : unitInterval ×
      ((X : Type u) ⊕ ((A ⊗ TopCat.I : TopCat.{u}) ⊕
        (𝟙_ TopCat.{u} : TopCat.{u}))) ≃ₜ _).continuous
    convert hcomp using 1
    funext p
    rcases p with ⟨t, x | r⟩
    · change _ = K (Homeomorph.prodSumDistrib (t, Sum.inl x))
      rw [show (Homeomorph.prodSumDistrib (t, Sum.inl x) :
        (unitInterval × (X : Type u)) ⊕ _) = Sum.inl (t, x) from rfl]
      rfl
    · change _ = K (Homeomorph.prodSumDistrib (t, Sum.inr r))
      rw [show (Homeomorph.prodSumDistrib (t, Sum.inr r) :
        (unitInterval × (X : Type u)) ⊕ _) = Sum.inr (t, r) from rfl]
      rcases r with c | z <;> rfl

@[simp]
theorem mappingConeMiddleDeformAmbientRaw_inl
    (f : A ⟶ X) [Nonempty A] (t : unitInterval) (x : X) :
    mappingConeMiddleDeformAmbientRaw f (t, Sum.inl x) =
      (mappingConeMiddleIncl f (Classical.choice inferInstance)).1 := rfl

@[simp]
theorem mappingConeMiddleDeformAmbientRaw_cylinder
    (f : A ⟶ X) [Nonempty A] (t : unitInterval)
    (c : (A ⊗ TopCat.I : TopCat.{u})) :
    mappingConeMiddleDeformAmbientRaw f (t, Sum.inr (Sum.inl c)) =
      topologicalMappingConeConeIncl f
        (topologicalConeCylinderIncl A (c.1, TopCat.I.midpointLerp
          (c.2, TopCat.I.homeomorph.symm t))) := rfl

@[simp]
theorem mappingConeMiddleDeformAmbientRaw_point
    (f : A ⟶ X) [Nonempty A] (t : unitInterval)
    (z : (𝟙_ TopCat.{u} : TopCat.{u})) :
    mappingConeMiddleDeformAmbientRaw f (t, Sum.inr (Sum.inr z)) =
      (mappingConeMiddleIncl f (Classical.choice inferInstance)).1 := rfl

/-- The middle interpolation formula, restricted and bundled with the fact that convex
interpolation with the midpoint stays in the overlap. -/
noncomputable def mappingConeMiddleDeformRaw
    (f : A ⟶ X) [Nonempty A] :
    C(unitInterval ×
      (topologicalMappingConeTripleDesc f ⁻¹' mappingConeMiddle f),
      mappingConeMiddle f) where
  toFun p := ⟨mappingConeMiddleDeformAmbientRaw f (p.1, p.2.1), by
    rcases p.2 with ⟨s, hs⟩
    change topologicalMappingConeTripleDesc f s ∈ mappingConeUpper f ∧
      topologicalMappingConeTripleDesc f s ∈ mappingConeLower f at hs
    rcases s with x | (c | z)
    · rw [mappingConeMiddleDeformAmbientRaw_inl]
      exact (mappingConeMiddleIncl f (Classical.choice inferInstance)).property
    · rw [mappingConeMiddleDeformAmbientRaw_cylinder]
      change 1 / 3 < topologicalMappingConeHeightReal f
          (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A
            (c.1, TopCat.I.midpointLerp
              (c.2, TopCat.I.homeomorph.symm p.1)))) ∧
        topologicalMappingConeHeightReal f
          (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A
            (c.1, TopCat.I.midpointLerp
              (c.2, TopCat.I.homeomorph.symm p.1)))) < 2 / 3
      unfold topologicalMappingConeHeightReal
      rw [show topologicalMappingConeHeight f
          (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A
            (c.1, TopCat.I.midpointLerp (c.2, TopCat.I.homeomorph.symm p.1)))) =
          topologicalConeHeight A (topologicalConeCylinderIncl A
            (c.1, TopCat.I.midpointLerp (c.2, TopCat.I.homeomorph.symm p.1))) from
        ConcreteCategory.congr_hom (topologicalMappingConeConeIncl_height f) _]
      rw [show topologicalConeHeight A (topologicalConeCylinderIncl A
          (c.1, TopCat.I.midpointLerp (c.2, TopCat.I.homeomorph.symm p.1))) =
          TopCat.I.midpointLerp (c.2, TopCat.I.homeomorph.symm p.1) from
        ConcreteCategory.congr_hom (topologicalConeCylinderIncl_height A) _]
      apply TopCat.I.midpointLerp_mem_thirds
      · have hsU := hs.1
        change 1 / 3 < topologicalMappingConeHeightReal f
          (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))) at hsU
        simpa only [topologicalMappingConeTripleDesc_cylinder_heightReal] using hsU
      · have hsL := hs.2
        change topologicalMappingConeHeightReal f
          (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))) < 2 / 3 at hsL
        simpa only [topologicalMappingConeTripleDesc_cylinder_heightReal] using hsL
    · rw [mappingConeMiddleDeformAmbientRaw_point]
      exact (mappingConeMiddleIncl f (Classical.choice inferInstance)).property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (mappingConeMiddleDeformAmbientRaw f).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- At every time, the middle-collar interpolation is constant on fibres of the restricted
mapping-cone quotient. -/
theorem mappingConeMiddleDeformRaw_factors
    (f : A ⟶ X) [Nonempty A] (t : unitInterval) :
    Function.FactorsThrough
      (fun p : topologicalMappingConeTripleDesc f ⁻¹' mappingConeMiddle f ↦
        mappingConeMiddleDeformRaw f (t, p))
      (mappingConeMiddleQuotient f) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
  have hpq' : topologicalMappingConeTripleDesc f p =
      topologicalMappingConeTripleDesc f q := congrArg Subtype.val hpq
  change topologicalMappingConeTripleDesc f p ∈ mappingConeUpper f ∧
    topologicalMappingConeTripleDesc f p ∈ mappingConeLower f at hp
  change topologicalMappingConeTripleDesc f q ∈ mappingConeUpper f ∧
    topologicalMappingConeTripleDesc f q ∈ mappingConeLower f at hq
  rcases p with x | (c | z)
  · exact (topologicalMappingConeTripleDesc_inl_not_mem_upper f x hp.1).elim
  · rcases q with y | (d | w)
    · exact (topologicalMappingConeTripleDesc_inl_not_mem_upper f y hq.1).elim
    · apply SetCoe.ext
      change topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A
          (c.1, TopCat.I.midpointLerp (c.2, TopCat.I.homeomorph.symm t))) =
        topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A
          (d.1, TopCat.I.midpointLerp (d.2, TopCat.I.homeomorph.symm t)))
      have hcone : topologicalConeCylinderIncl A c =
          topologicalConeCylinderIncl A d := by
        apply topologicalMappingConeConeIncl_eq_of_height_pos f
        · have hpU := hp.1
          change 1 / 3 < topologicalMappingConeHeightReal f
            (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))) at hpU
          change 1 / 3 < topologicalMappingConeHeightReal f
            (topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A c)) at hpU
          linarith
        · exact hpq'
      have hcd : c = d := by
        apply topologicalConeCylinderIncl_eq_iff_below c d
        · have hpL := hp.2
          change topologicalMappingConeHeightReal f
            (topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))) < 2 / 3 at hpL
          simpa only [topologicalMappingConeTripleDesc_cylinder_heightReal] using hpL
        · exact hcone
      rw [hcd]
    · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f w hq.2).elim
  · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f z hp.2).elim

/-- The raw middle-collar interpolation at a fixed time. -/
def mappingConeMiddleDeformRawAt
    (f : A ⟶ X) [Nonempty A] (t : unitInterval) :
    C(topologicalMappingConeTripleDesc f ⁻¹' mappingConeMiddle f,
      mappingConeMiddle f) where
  toFun p := mappingConeMiddleDeformRaw f (t, p)
  continuous_toFun := (mappingConeMiddleDeformRaw f).continuous.comp
    (continuous_const.prodMk continuous_id)

/-- The descended middle-collar interpolation at a fixed time. -/
noncomputable def mappingConeMiddleDeformAt
    (f : A ⟶ X) [Nonempty A] (t : unitInterval) :
    TopCat.of (mappingConeMiddle f) ⟶ TopCat.of (mappingConeMiddle f) :=
  TopCat.ofHom ((mappingConeMiddleQuotient_isQuotientMap f).lift
    (mappingConeMiddleDeformRawAt f t) (mappingConeMiddleDeformRaw_factors f t))

@[simp]
theorem mappingConeMiddleDeformAt_quotient
    (f : A ⟶ X) [Nonempty A] (t : unitInterval)
    (p : topologicalMappingConeTripleDesc f ⁻¹' mappingConeMiddle f) :
    mappingConeMiddleDeformAt f t (mappingConeMiddleQuotient f p) =
      mappingConeMiddleDeformRaw f (t, p) := by
  exact ContinuousMap.congr_fun ((mappingConeMiddleQuotient_isQuotientMap f).lift_comp
    (mappingConeMiddleDeformRawAt f t) (mappingConeMiddleDeformRaw_factors f t)) p

theorem continuous_mappingConeMiddleDeformAt
    (f : A ⟶ X) [Nonempty A] :
    Continuous (fun p : unitInterval × mappingConeMiddle f ↦
      mappingConeMiddleDeformAt f p.1 p.2) := by
  apply (mappingConeMiddleQuotient_isQuotientMap f).continuous_lift_prod_right
  convert (mappingConeMiddleDeformRaw f).continuous using 1
  funext p
  rw [mappingConeMiddleDeformAt_quotient]

theorem mappingConeMiddleDeformAt_zero
    (f : A ⟶ X) [Nonempty A] (z : mappingConeMiddle f) :
    mappingConeMiddleDeformAt f 0 z =
      (mappingConeMiddleRetract f ≫ mappingConeMiddleIncl f) z := by
  obtain ⟨p, rfl⟩ := (mappingConeMiddleQuotient_isQuotientMap f).surjective z
  rw [mappingConeMiddleDeformAt_quotient]
  rcases p with ⟨s, hs⟩
  change topologicalMappingConeTripleDesc f s ∈ mappingConeUpper f ∧
    topologicalMappingConeTripleDesc f s ∈ mappingConeLower f at hs
  rcases s with x | (c | w)
  · exact (topologicalMappingConeTripleDesc_inl_not_mem_upper f x hs.1).elim
  · change mappingConeMiddleDeformRaw f
        (0, ⟨Sum.inr (Sum.inl c), hs⟩) =
      mappingConeMiddleIncl f
        (mappingConeMiddleRetract f
          (mappingConeMiddleQuotient f ⟨Sum.inr (Sum.inl c), hs⟩))
    rw [mappingConeMiddleRetract_quotient]
    apply SetCoe.ext
    change topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A
        (c.1, TopCat.I.midpointLerp (c.2, TopCat.I.homeomorph.symm 0))) =
      topologicalMappingConeConeIncl f
        (topologicalConeCylinderIncl A (c.1, TopCat.I.midpoint))
    rw [show TopCat.I.homeomorph.symm (0 : unitInterval) = 0 by rfl,
      TopCat.I.midpointLerp_zero]
  · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f w hs.2).elim

theorem mappingConeMiddleDeformAt_one
    (f : A ⟶ X) [Nonempty A] (z : mappingConeMiddle f) :
    mappingConeMiddleDeformAt f 1 z = z := by
  obtain ⟨p, rfl⟩ := (mappingConeMiddleQuotient_isQuotientMap f).surjective z
  rw [mappingConeMiddleDeformAt_quotient]
  rcases p with ⟨s, hs⟩
  change topologicalMappingConeTripleDesc f s ∈ mappingConeUpper f ∧
    topologicalMappingConeTripleDesc f s ∈ mappingConeLower f at hs
  rcases s with x | (c | w)
  · exact (topologicalMappingConeTripleDesc_inl_not_mem_upper f x hs.1).elim
  · apply SetCoe.ext
    change topologicalMappingConeConeIncl f (topologicalConeCylinderIncl A
        (c.1, TopCat.I.midpointLerp (c.2, TopCat.I.homeomorph.symm 1))) =
      topologicalMappingConeTripleDesc f (Sum.inr (Sum.inl c))
    rw [show TopCat.I.homeomorph.symm (1 : unitInterval) = 1 by rfl,
      TopCat.I.midpointLerp_one]
    rfl
  · exact (topologicalMappingConeTripleDesc_point_not_mem_lower f w hs.2).elim

/-- Deformation of the middle collar to the midpoint copy of the attaching space. -/
noncomputable def mappingConeMiddleDeformation
    (f : A ⟶ X) [Nonempty A] :
    TopCat.Homotopy (mappingConeMiddleRetract f ≫ mappingConeMiddleIncl f)
      (𝟙 (TopCat.of (mappingConeMiddle f))) where
  toFun p := mappingConeMiddleDeformAt f p.1 p.2
  continuous_toFun := continuous_mappingConeMiddleDeformAt f
  map_zero_left z := mappingConeMiddleDeformAt_zero f z
  map_one_left z := mappingConeMiddleDeformAt_one f z

/-- The overlap of the standard mapping-cone cover is homotopy equivalent to the attaching
space. -/
noncomputable def mappingConeMiddleHomotopyEquiv
    (f : A ⟶ X) [Nonempty A] :
    ContinuousMap.HomotopyEquiv (mappingConeMiddle f) A where
  toFun := (mappingConeMiddleRetract f).hom
  invFun := (mappingConeMiddleIncl f).hom
  left_inv := ⟨mappingConeMiddleDeformation f⟩
  right_inv := by
    have h : mappingConeMiddleIncl f ≫ mappingConeMiddleRetract f = 𝟙 A := by
      ext a
      exact mappingConeMiddleRetract_incl f a
    rw [← TopCat.hom_comp, h, TopCat.hom_id]

/-- Path connectedness transfers across a homotopy equivalence. -/
theorem pathConnectedSpace_of_homotopyEquiv
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    [PathConnectedSpace Z] (e : ContinuousMap.HomotopyEquiv Y Z) :
    PathConnectedSpace Y := by
  let H := e.left_inv.some
  let pathTo (y : Y) : Path ((e.invFun.comp e.toFun) y) y :=
    ⟨⟨fun t ↦ H (t, y), H.continuous.comp
        (continuous_id.prodMk continuous_const)⟩,
      H.map_zero_left y, H.map_one_left y⟩
  refine ⟨⟨e.invFun (Classical.choice (inferInstance : Nonempty Z))⟩, ?_⟩
  intro y z
  have hyz : Joined (e.invFun (e y)) (e.invFun (e z)) :=
    ⟨(PathConnectedSpace.somePath (e y) (e z)).map e.invFun.continuous⟩
  exact (show Joined y ((e.invFun.comp e.toFun) y) from ⟨(pathTo y).symm⟩).trans
    (hyz.trans (show Joined ((e.invFun.comp e.toFun) z) z from ⟨pathTo z⟩))

/-- The lower collar is path connected when the mapping-cone target is. -/
theorem pathConnectedSpace_mappingConeLower
    (f : A ⟶ X) [PathConnectedSpace X] :
    PathConnectedSpace (mappingConeLower f) :=
  pathConnectedSpace_of_homotopyEquiv
    (mappingConeLowerHomotopyEquiv f)

/-- The overlap in the standard mapping-cone cover is path connected when the attaching
space is. -/
theorem pathConnectedSpace_mappingConeMiddle
    (f : A ⟶ X) [PathConnectedSpace A] :
    PathConnectedSpace (mappingConeMiddle f) :=
  pathConnectedSpace_of_homotopyEquiv
    (mappingConeMiddleHomotopyEquiv f)

/-- A mapping cone with path-connected target and nonempty attaching space is path connected. -/
theorem pathConnectedSpace_topologicalMappingCone
    (f : A ⟶ X) [Nonempty A] [PathConnectedSpace X] :
    PathConnectedSpace (topologicalMappingCone f) := by
  letI : PathConnectedSpace (mappingConeLower f) :=
    pathConnectedSpace_mappingConeLower f
  have hUpper : IsPathConnected (mappingConeUpper f) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hLower : IsPathConnected (mappingConeLower f) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hMeet : (mappingConeUpper f ∩ mappingConeLower f).Nonempty := by
    let a := Classical.choice (inferInstance : Nonempty A)
    exact ⟨(mappingConeMiddleIncl f a).1, (mappingConeMiddleIncl f a).2⟩
  rw [pathConnectedSpace_iff_univ, ← mappingConeUpper_union_lower f]
  exact hUpper.union hLower hMeet

end Submission
