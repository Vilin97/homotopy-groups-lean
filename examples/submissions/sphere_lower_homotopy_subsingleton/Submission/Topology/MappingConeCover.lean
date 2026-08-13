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

universe u

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

end Submission
