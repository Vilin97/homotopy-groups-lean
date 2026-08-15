/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.MappingConeCover

/-!
# Functoriality of the mapping-cone height cover

Maps of topological mapping cones preserve the cone-height coordinate.  Consequently they carry
the standard lower, upper, and middle collars into the corresponding collars, with each source
collar exactly the preimage of its target counterpart.
-/

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory
  CartesianMonoidalCategory

noncomputable section

namespace Submission

universe u

/-- Applying a map to the space coordinate of a topological cone preserves its height. -/
theorem topologicalConeMap_height {A B : TopCat.{u}} (a : A ⟶ B) :
    topologicalConeMap a ≫ topologicalConeHeight B =
      topologicalConeHeight A := by
  apply topologicalCone_hom_ext A
  · simp only [topologicalConeCylinderIncl_map_assoc,
      topologicalConeCylinderIncl_height]
    apply TopCat.hom_ext
    ext p
    rfl
  · simp only [topologicalConePointIncl_map_assoc,
      topologicalConePointIncl_height]

/-- A map induced by a commutative square of attaching maps preserves mapping-cone height. -/
theorem topologicalMappingConeMap_height
    {A B X Y : TopCat.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (a : A ⟶ B) (x : X ⟶ Y)
    (h : f ≫ x = a ≫ g) :
    topologicalMappingConeMap f g a x h ≫ topologicalMappingConeHeight g =
      topologicalMappingConeHeight f := by
  apply topologicalMappingCone_hom_ext f
  · simp only [topologicalMappingConeIncl_map_assoc,
      topologicalMappingConeIncl_height]
    apply TopCat.hom_ext
    ext p
    rfl
  · simp only [topologicalMappingConeConeIncl_map_assoc,
      topologicalConeMap_height,
      topologicalMappingConeConeIncl_height]

/-- Pointwise real-valued form of mapping-cone height preservation. -/
@[simp]
theorem topologicalMappingConeMap_heightReal_apply
    {A B X Y : TopCat.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (a : A ⟶ B) (x : X ⟶ Y)
    (h : f ≫ x = a ≫ g) (p : topologicalMappingCone f) :
    topologicalMappingConeHeightReal g
        (topologicalMappingConeMap f g a x h p) =
      topologicalMappingConeHeightReal f p := by
  unfold topologicalMappingConeHeightReal
  rw [show topologicalMappingConeHeight g
      (topologicalMappingConeMap f g a x h p) =
      topologicalMappingConeHeight f p from
    ConcreteCategory.congr_hom
      (topologicalMappingConeMap_height f g a x h) p]

/-- The lower source collar is exactly the preimage of the lower target collar. -/
theorem topologicalMappingConeMap_preimage_lower
    {A B X Y : TopCat.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (a : A ⟶ B) (x : X ⟶ Y)
    (h : f ≫ x = a ≫ g) :
    topologicalMappingConeMap f g a x h ⁻¹' mappingConeLower g =
      mappingConeLower f := by
  ext p
  change topologicalMappingConeHeightReal g
      (topologicalMappingConeMap f g a x h p) < 2 / 3 ↔
    topologicalMappingConeHeightReal f p < 2 / 3
  rw [topologicalMappingConeMap_heightReal_apply]

/-- The upper source collar is exactly the preimage of the upper target collar. -/
theorem topologicalMappingConeMap_preimage_upper
    {A B X Y : TopCat.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (a : A ⟶ B) (x : X ⟶ Y)
    (h : f ≫ x = a ≫ g) :
    topologicalMappingConeMap f g a x h ⁻¹' mappingConeUpper g =
      mappingConeUpper f := by
  ext p
  change 1 / 3 < topologicalMappingConeHeightReal g
      (topologicalMappingConeMap f g a x h p) ↔
    1 / 3 < topologicalMappingConeHeightReal f p
  rw [topologicalMappingConeMap_heightReal_apply]

/-- The middle source collar is exactly the preimage of the middle target collar. -/
theorem topologicalMappingConeMap_preimage_middle
    {A B X Y : TopCat.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (a : A ⟶ B) (x : X ⟶ Y)
    (h : f ≫ x = a ≫ g) :
    topologicalMappingConeMap f g a x h ⁻¹' mappingConeMiddle g =
      mappingConeMiddle f := by
  simp only [mappingConeMiddle, Set.preimage_inter,
    topologicalMappingConeMap_preimage_upper,
    topologicalMappingConeMap_preimage_lower]

/-- The cofiber collapse with its target normalized to the literal mapping cone of the map to
the terminal space. -/
def topologicalMappingConeCollapseToMappingCone
    {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalMappingCone f ⟶ topologicalMappingCone (toUnit A) :=
  topologicalMappingConeMap f (toUnit A) (𝟙 A) (toUnit X) (by
    apply toUnit_unique)

@[reassoc (attr := simp)]
theorem topologicalMappingConeIncl_collapseToMappingCone
    {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalMappingConeIncl f ≫
        topologicalMappingConeCollapseToMappingCone f =
      toUnit X ≫ topologicalMappingConeIncl (toUnit A) :=
  topologicalMappingConeIncl_map f (toUnit A) (𝟙 A) (toUnit X) _

@[reassoc (attr := simp)]
theorem topologicalMappingConeConeIncl_collapseToMappingCone
    {A X : TopCat.{u}} (f : A ⟶ X) :
    topologicalMappingConeConeIncl f ≫
        topologicalMappingConeCollapseToMappingCone f =
      topologicalMappingConeConeIncl (toUnit A) := by
  unfold topologicalMappingConeCollapseToMappingCone
  rw [topologicalMappingConeConeIncl_map, topologicalConeMap_id,
    Category.id_comp]

/-- The unique map from a nonempty space to the terminal topological space is a quotient map. -/
theorem topologicalToUnit_isQuotientMap (X : TopCat.{u}) [Nonempty X] :
    IsQuotientMap (toUnit X) := by
  have hUnit (z w : ((𝟙_ TopCat.{u} : TopCat.{u}) : Type u)) : z = w := by
    let cz : X ⟶ (𝟙_ TopCat.{u} : TopCat.{u}) :=
      TopCat.ofHom ⟨fun _ ↦ z, continuous_const⟩
    let cw : X ⟶ (𝟙_ TopCat.{u} : TopCat.{u}) :=
      TopCat.ofHom ⟨fun _ ↦ w, continuous_const⟩
    exact ConcreteCategory.congr_hom (toUnit_unique cz cw)
      (Classical.choice inferInstance)
  apply IsOpenMap.isQuotientMap
  · intro U _hU
    rcases U.eq_empty_or_nonempty with rfl | hU
    · simpa only [Set.image_empty] using
        (isOpen_empty : IsOpen (∅ : Set ((𝟙_ TopCat.{u} : TopCat.{u}) : Type u)))
    · have hImage : toUnit X '' U = Set.univ := by
        ext z
        simp only [Set.mem_image, Set.mem_univ, iff_true]
        obtain ⟨x, hx⟩ := hU
        exact ⟨x, hx, hUnit _ _⟩
      rw [hImage]
      exact isOpen_univ
  · exact (toUnit X).hom.continuous
  · intro z
    exact ⟨Classical.choice inferInstance, hUnit _ z⟩

/-- Collapsing the original-space summand of a mapping cone is a quotient map whenever that
summand is nonempty. -/
theorem topologicalMappingConeCollapse_isQuotientMap
    {A X : TopCat.{u}} (f : A ⟶ X) [Nonempty X] :
    IsQuotientMap (topologicalMappingConeCollapse f) := by
  let q : (X : Type u) ⊕ (topologicalCone A : Type u) →
      (((𝟙_ TopCat.{u} : TopCat.{u}) : Type u) ⊕
        (topologicalCone A : Type u)) :=
    Sum.map (toUnit X) id
  have hq : IsQuotientMap q :=
    IsQuotientMap.sumMap (topologicalToUnit_isQuotientMap X) IsQuotientMap.id
  have hTarget : IsQuotientMap
      (pushoutSumDesc (toUnit A) (topologicalConeBaseIncl A)) :=
    pushoutSumDesc_isQuotientMap (toUnit A) (topologicalConeBaseIncl A)
  have hComp : IsQuotientMap
      (pushoutSumDesc (toUnit A) (topologicalConeBaseIncl A) ∘ q) :=
    hTarget.comp hq
  have hComm :
      topologicalMappingConeCollapse f ∘
          pushoutSumDesc f (topologicalConeBaseIncl A) =
        pushoutSumDesc (toUnit A) (topologicalConeBaseIncl A) ∘ q := by
    funext z
    rcases z with x | c
    · exact ConcreteCategory.congr_hom
        (topologicalMappingConeIncl_collapse f) x
    · exact ConcreteCategory.congr_hom
        (topologicalMappingConeConeIncl_collapse f) c
  rw [← hComm] at hComp
  exact (pushoutSumDesc_isQuotientMap f
    (topologicalConeBaseIncl A)).of_comp_isQuotientMap hComp

/-- Every positive-height point of a mapping cone is represented by its cone summand. -/
theorem exists_topologicalMappingConeConeIncl_of_heightReal_pos
    {A X : TopCat.{u}} (f : A ⟶ X) (p : topologicalMappingCone f)
    (hp : 0 < topologicalMappingConeHeightReal f p) :
    ∃ c : topologicalCone A, topologicalMappingConeConeIncl f c = p := by
  obtain ⟨z, rfl⟩ := (topologicalMappingConeTripleDesc_isQuotientMap f).surjective p
  rcases z with x | (c | z)
  · simp only [topologicalMappingConeTripleDesc_inl_heightReal] at hp
    linarith
  · exact ⟨topologicalConeCylinderIncl A c, rfl⟩
  · exact ⟨topologicalConePointIncl A z, rfl⟩

/-- The cofiber collapse is injective between positive-height points: all identifications made
by the collapse occur in the original-space summand at height zero. -/
theorem topologicalMappingConeCollapse_injective_of_heightReal_pos
    {A X : TopCat.{u}} (f : A ⟶ X) (p q : topologicalMappingCone f)
    (hp : 0 < topologicalMappingConeHeightReal f p)
    (hq : 0 < topologicalMappingConeHeightReal f q)
    (h : topologicalMappingConeCollapse f p = topologicalMappingConeCollapse f q) :
    p = q := by
  obtain ⟨c, rfl⟩ :=
    exists_topologicalMappingConeConeIncl_of_heightReal_pos f p hp
  obtain ⟨d, rfl⟩ :=
    exists_topologicalMappingConeConeIncl_of_heightReal_pos f q hq
  apply congrArg (topologicalMappingConeConeIncl f)
  apply topologicalMappingConeConeIncl_eq_of_height_pos (toUnit A) c d
  · unfold topologicalMappingConeHeightReal at hp ⊢
    rw [show topologicalMappingConeHeight f
        (topologicalMappingConeConeIncl f c) = topologicalConeHeight A c from
      ConcreteCategory.congr_hom (topologicalMappingConeConeIncl_height f) c] at hp
    rw [show topologicalMappingConeHeight (toUnit A)
        (topologicalMappingConeConeIncl (toUnit A) c) = topologicalConeHeight A c from
      ConcreteCategory.congr_hom
        (topologicalMappingConeConeIncl_height (toUnit A)) c]
    exact hp
  · change (topologicalMappingConeConeIncl f ≫
        topologicalMappingConeCollapse f) c =
      (topologicalMappingConeConeIncl f ≫
        topologicalMappingConeCollapse f) d at h
    have hc := ConcreteCategory.congr_hom
      (topologicalMappingConeConeIncl_collapse f) c
    have hd := ConcreteCategory.congr_hom
      (topologicalMappingConeConeIncl_collapse f) d
    unfold topologicalSuspensionConeIncl topologicalSuspension at hc hd
    exact hc.symm.trans (h.trans hd)

/-- The cofiber collapse restricted to the lower mapping-cone collar. -/
def topologicalMappingConeCollapseLower
    {A X : TopCat.{u}} (f : A ⟶ X) :
    TopCat.of (mappingConeLower f) ⟶
      TopCat.of (mappingConeLower (toUnit A)) := by
  apply TopCat.ofHom
  refine ⟨fun p ↦ ⟨topologicalMappingConeCollapse f p, ?_⟩, ?_⟩
  · have hpre : topologicalMappingConeCollapse f ⁻¹' mappingConeLower (toUnit A) =
        mappingConeLower f := by
      exact topologicalMappingConeMap_preimage_lower f (toUnit A) (𝟙 A)
        (toUnit X) (by apply toUnit_unique)
    change p.1 ∈ topologicalMappingConeCollapse f ⁻¹'
      mappingConeLower (toUnit A)
    rw [hpre]
    exact p.property
  · apply Continuous.subtype_mk
    exact (topologicalMappingConeCollapse f).hom.continuous.comp continuous_subtype_val

/-- The original-space inclusions into the lower collars commute with cofiber collapse. -/
@[reassoc]
theorem mappingConeLowerIncl_collapseLower
    {A X : TopCat.{u}} (f : A ⟶ X) :
    mappingConeLowerIncl f ≫ topologicalMappingConeCollapseLower f =
      toUnit X ≫ mappingConeLowerIncl (toUnit A) := by
  ext x
  exact ConcreteCategory.congr_hom (topologicalMappingConeIncl_collapse f) x

/-- The cofiber collapse restricted to the upper mapping-cone collar. -/
def topologicalMappingConeCollapseUpper
    {A X : TopCat.{u}} (f : A ⟶ X) :
    TopCat.of (mappingConeUpper f) ⟶
      TopCat.of (mappingConeUpper (toUnit A)) := by
  apply TopCat.ofHom
  refine ⟨fun p ↦ ⟨topologicalMappingConeCollapse f p, ?_⟩, ?_⟩
  · have hpre : topologicalMappingConeCollapse f ⁻¹' mappingConeUpper (toUnit A) =
        mappingConeUpper f := by
      exact topologicalMappingConeMap_preimage_upper f (toUnit A) (𝟙 A)
        (toUnit X) (by apply toUnit_unique)
    change p.1 ∈ topologicalMappingConeCollapse f ⁻¹'
      mappingConeUpper (toUnit A)
    rw [hpre]
    exact p.property
  · apply Continuous.subtype_mk
    exact (topologicalMappingConeCollapse f).hom.continuous.comp continuous_subtype_val

/-- The upper-collar restriction of a cofiber collapse is a quotient map. -/
theorem topologicalMappingConeCollapseUpper_isQuotientMap
    {A X : TopCat.{u}} (f : A ⟶ X) [Nonempty X] :
    IsQuotientMap (topologicalMappingConeCollapseUpper f) := by
  have hq := (topologicalMappingConeCollapse_isQuotientMap f).restrictPreimage_isOpen
    (isOpen_mappingConeUpper (toUnit A))
  have hpre : topologicalMappingConeCollapse f ⁻¹' mappingConeUpper (toUnit A) =
      mappingConeUpper f := by
    exact topologicalMappingConeMap_preimage_upper f (toUnit A) (𝟙 A)
      (toUnit X) (by apply toUnit_unique)
  have hcomp := hq.comp (Homeomorph.setCongr hpre.symm).isQuotientMap
  have heq : (topologicalMappingConeCollapseUpper f :
        mappingConeUpper f → mappingConeUpper (toUnit A)) =
      (mappingConeUpper (toUnit A)).restrictPreimage
          (topologicalMappingConeCollapse f) ∘
        (Homeomorph.setCongr hpre.symm :
          mappingConeUpper f →
            topologicalMappingConeCollapse f ⁻¹' mappingConeUpper (toUnit A)) := by
    funext p
    apply SetCoe.ext
    rfl
  rw [heq]
  exact hcomp

/-- The upper-collar restriction of a cofiber collapse is injective. -/
theorem topologicalMappingConeCollapseUpper_injective
    {A X : TopCat.{u}} (f : A ⟶ X) :
    Function.Injective (topologicalMappingConeCollapseUpper f) := by
  intro p q h
  apply SetCoe.ext
  apply topologicalMappingConeCollapse_injective_of_heightReal_pos f p q
  · exact lt_trans (by norm_num) p.property
  · exact lt_trans (by norm_num) q.property
  · exact congrArg Subtype.val h

/-- The cofiber collapse is a homeomorphism on the upper mapping-cone collar. -/
theorem topologicalMappingConeCollapseUpper_isHomeomorph
    {A X : TopCat.{u}} (f : A ⟶ X) [Nonempty X] :
    IsHomeomorph (topologicalMappingConeCollapseUpper f) :=
  isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨topologicalMappingConeCollapseUpper_isQuotientMap f,
      topologicalMappingConeCollapseUpper_injective f⟩

instance topologicalMappingConeCollapseUpper_isIso
    {A X : TopCat.{u}} (f : A ⟶ X) [Nonempty X] :
    IsIso (topologicalMappingConeCollapseUpper f) :=
  (TopCat.isIso_iff_isHomeomorph
    (topologicalMappingConeCollapseUpper f)).mpr
      (topologicalMappingConeCollapseUpper_isHomeomorph f)

/-- The cofiber collapse restricted to the overlap of the upper and lower collars. -/
def topologicalMappingConeCollapseMiddle
    {A X : TopCat.{u}} (f : A ⟶ X) :
    TopCat.of (mappingConeUpper f ∩ mappingConeLower f :
        Set (topologicalMappingCone f)) ⟶
      TopCat.of (mappingConeUpper (toUnit A) ∩ mappingConeLower (toUnit A) :
        Set (topologicalMappingCone (toUnit A))) := by
  apply TopCat.ofHom
  refine ⟨fun p ↦ ⟨topologicalMappingConeCollapse f p, ?_⟩, ?_⟩
  · have hpre : topologicalMappingConeCollapse f ⁻¹' mappingConeMiddle (toUnit A) =
        mappingConeMiddle f := by
      exact topologicalMappingConeMap_preimage_middle f (toUnit A) (𝟙 A)
        (toUnit X) (by apply toUnit_unique)
    change p.1 ∈ topologicalMappingConeCollapse f ⁻¹'
      mappingConeMiddle (toUnit A)
    rw [hpre]
    exact p.property
  · apply Continuous.subtype_mk
    exact (topologicalMappingConeCollapse f).hom.continuous.comp continuous_subtype_val

/-- The overlap-collar restriction of a cofiber collapse is a quotient map. -/
theorem topologicalMappingConeCollapseMiddle_isQuotientMap
    {A X : TopCat.{u}} (f : A ⟶ X) [Nonempty X] :
    IsQuotientMap (topologicalMappingConeCollapseMiddle f) := by
  have hq := (topologicalMappingConeCollapse_isQuotientMap f).restrictPreimage_isOpen
    (isOpen_mappingConeMiddle (toUnit A))
  have hpre : topologicalMappingConeCollapse f ⁻¹' mappingConeMiddle (toUnit A) =
      mappingConeMiddle f := by
    exact topologicalMappingConeMap_preimage_middle f (toUnit A) (𝟙 A)
      (toUnit X) (by apply toUnit_unique)
  have hcomp := hq.comp (Homeomorph.setCongr hpre.symm).isQuotientMap
  have heq : (topologicalMappingConeCollapseMiddle f :
        mappingConeMiddle f → mappingConeMiddle (toUnit A)) =
      (mappingConeMiddle (toUnit A)).restrictPreimage
          (topologicalMappingConeCollapse f) ∘
        (Homeomorph.setCongr hpre.symm :
          mappingConeMiddle f →
            topologicalMappingConeCollapse f ⁻¹' mappingConeMiddle (toUnit A)) := by
    funext p
    apply SetCoe.ext
    rfl
  rw [heq]
  exact hcomp

/-- The overlap-collar restriction of a cofiber collapse is injective. -/
theorem topologicalMappingConeCollapseMiddle_injective
    {A X : TopCat.{u}} (f : A ⟶ X) :
    Function.Injective (topologicalMappingConeCollapseMiddle f) := by
  intro p q h
  apply SetCoe.ext
  apply topologicalMappingConeCollapse_injective_of_heightReal_pos f p q
  · exact lt_trans (by norm_num) p.property.1
  · exact lt_trans (by norm_num) q.property.1
  · exact congrArg Subtype.val h

/-- The cofiber collapse is a homeomorphism on the overlap of the standard collars. -/
theorem topologicalMappingConeCollapseMiddle_isHomeomorph
    {A X : TopCat.{u}} (f : A ⟶ X) [Nonempty X] :
    IsHomeomorph (topologicalMappingConeCollapseMiddle f) :=
  isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨topologicalMappingConeCollapseMiddle_isQuotientMap f,
      topologicalMappingConeCollapseMiddle_injective f⟩

instance topologicalMappingConeCollapseMiddle_isIso
    {A X : TopCat.{u}} (f : A ⟶ X) [Nonempty X] :
    IsIso (topologicalMappingConeCollapseMiddle f) :=
  (TopCat.isIso_iff_isHomeomorph
    (topologicalMappingConeCollapseMiddle f)).mpr
      (topologicalMappingConeCollapseMiddle_isHomeomorph f)

end Submission
