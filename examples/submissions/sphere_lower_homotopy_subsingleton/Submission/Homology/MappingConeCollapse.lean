/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.Excision
import Submission.Homology.MappingCone
import Submission.Topology.MappingConeCoverMap

/-!
# Relative homology of the mapping-cone collapse

The cofiber collapse is an isomorphism away from the original-space summand.  Applying
relative excision to the standard height cover turns this geometric observation into an
isomorphism on the relative homology of the lower-collar pair, and hence on the relative
homology of the original mapping-cone pair.
-/

open CategoryTheory Limits AlgebraicTopology MonoidalCategory
  CartesianMonoidalCategory Topology

noncomputable section

namespace Submission

variable {A X B Y : TopCat.{0}}

/-- A map of pairs whose subspace and ambient maps are homotopy equivalences induces an
isomorphism on relative singular homology. -/
theorem isIso_HrelMap_of_homotopyEquiv
    (n : ℕ) (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j)
    (gA : B ⟶ A)
    (HA₁ : TopCat.Homotopy (fA ≫ gA) (𝟙 A))
    (HA₂ : TopCat.Homotopy (gA ≫ fA) (𝟙 B))
    (g : Y ⟶ X)
    (H₁ : TopCat.Homotopy (f ≫ g) (𝟙 X))
    (H₂ : TopCat.Homotopy (g ≫ f) (𝟙 Y)) :
    IsIso (HrelMap n i j w) := by
  apply HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (relShortComplexMap i j w) (relShortComplex_shortExact i)
      (relShortComplex_shortExact j)
  · change Epi (HgrpMap n fA)
    exact (hgrpIsoOfHomotopyEquiv fA gA HA₁ HA₂ n).isIso_hom.epi_of_iso
  · change IsIso (HgrpMap n f)
    exact (hgrpIsoOfHomotopyEquiv f g H₁ H₂ n).isIso_hom
  · intro k _
    change IsIso (HgrpMap k fA)
    exact (hgrpIsoOfHomotopyEquiv fA gA HA₁ HA₂ k).isIso_hom
  · intro k _
    change Mono (HgrpMap k f)
    exact (hgrpIsoOfHomotopyEquiv f g H₁ H₂ k).isIso_hom.mono_of_iso

/-- The induced relative map depends on the subspace and ambient maps, not on how equal maps
were presented or on the proof of the pair square. -/
theorem HrelMap_eq_of_maps_eq
    (n : ℕ) (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (w : i ≫ f = fA ≫ j) (w' : i ≫ g = gA ≫ j)
    (hA : fA = gA) (h : f = g) :
    HrelMap n i j w = HrelMap n i j w' := by
  subst gA
  subst g
  rfl

variable {A X : TopCat.{0}}

/-- Replace the original-space member of the mapping-cone pair by the lower collar. -/
def mappingConeLowerPairHrelMap (f : A ⟶ X) (n : ℕ) :
    Hrel n (topologicalMappingConeIncl f) ⟶
      Hrel n (subIncl (mappingConeLower f)) :=
  HrelMap n (topologicalMappingConeIncl f) (subIncl (mappingConeLower f))
    (show topologicalMappingConeIncl f ≫ 𝟙 (topologicalMappingCone f) =
      mappingConeLowerIncl f ≫ subIncl (mappingConeLower f) by rfl)

/-- Replacing the original-space member by the lower collar is a relative-homology
isomorphism. -/
theorem isIso_mappingConeLowerPairHrelMap
    (f : A ⟶ X) [Nonempty X] (n : ℕ) :
    IsIso (mappingConeLowerPairHrelMap f n) := by
  have hstrict : mappingConeLowerIncl f ≫ mappingConeLowerRetract f = 𝟙 X := by
    ext x
    exact mappingConeLowerRetract_incl f x
  let HA₁ : TopCat.Homotopy
      (mappingConeLowerIncl f ≫ mappingConeLowerRetract f) (𝟙 X) :=
    hstrict ▸ TopCat.Homotopy.refl (𝟙 X)
  let HI : TopCat.Homotopy
      ((𝟙 (topologicalMappingCone f)) ≫ (𝟙 (topologicalMappingCone f)))
      (𝟙 (topologicalMappingCone f)) := by
    rw [Category.id_comp]
    exact TopCat.Homotopy.refl _
  apply isIso_HrelMap_of_homotopyEquiv n
    (topologicalMappingConeIncl f) (subIncl (mappingConeLower f))
    (show topologicalMappingConeIncl f ≫ 𝟙 (topologicalMappingCone f) =
      mappingConeLowerIncl f ≫ subIncl (mappingConeLower f) by rfl)
    (mappingConeLowerRetract f) HA₁ (mappingConeLowerDeformation f)
    (𝟙 (topologicalMappingCone f)) HI HI

/-- The map of lower-collar pairs induced by cofiber collapse. -/
def mappingConeCollapseLowerHrelMap (f : A ⟶ X) (n : ℕ) :
    Hrel n (subIncl (mappingConeLower f)) ⟶
      Hrel n (subIncl (mappingConeLower (toUnit A))) :=
  HrelMap n (subIncl (mappingConeLower f))
    (subIncl (mappingConeLower (toUnit A)))
    (show subIncl (mappingConeLower f) ≫
        topologicalMappingConeCollapseToMappingCone f =
      topologicalMappingConeCollapseLower f ≫
        subIncl (mappingConeLower (toUnit A)) by rfl)

/-- On upper collars, restricting collapse and then including is the original collapse. -/
@[reassoc]
theorem topologicalMappingConeCollapseUpper_subIncl (f : A ⟶ X) :
    topologicalMappingConeCollapseUpper f ≫
        subIncl (mappingConeUpper (toUnit A)) =
      subIncl (mappingConeUpper f) ≫
        topologicalMappingConeCollapseToMappingCone f := by
  rfl

/-- The overlap-to-lower inclusions commute with the restricted cofiber collapse. -/
@[reassoc]
theorem mvInclRight_topologicalMappingConeCollapseLower (f : A ⟶ X) :
    mvInclRight (mappingConeUpper f) (mappingConeLower f) ≫
        topologicalMappingConeCollapseLower f =
      topologicalMappingConeCollapseMiddle f ≫
        mvInclRight (mappingConeUpper (toUnit A))
          (mappingConeLower (toUnit A)) := by
  rfl

/-- The map of upper-overlap collar pairs induced by cofiber collapse. -/
def mappingConeCollapseCollarHrelMap (f : A ⟶ X) (n : ℕ) :
    Hrel n (mvInclLeft (mappingConeUpper f) (mappingConeLower f)) ⟶
      Hrel n (mvInclLeft (mappingConeUpper (toUnit A))
        (mappingConeLower (toUnit A))) :=
  HrelMap n
    (mvInclLeft (mappingConeUpper f) (mappingConeLower f))
    (mvInclLeft (mappingConeUpper (toUnit A)) (mappingConeLower (toUnit A)))
    (show mvInclLeft (mappingConeUpper f) (mappingConeLower f) ≫
        topologicalMappingConeCollapseUpper f =
      topologicalMappingConeCollapseMiddle f ≫
        mvInclLeft (mappingConeUpper (toUnit A))
          (mappingConeLower (toUnit A)) by rfl)

/-- Collapse is a relative-homology isomorphism on the upper-overlap collar pair. -/
theorem isIso_mappingConeCollapseCollarHrelMap
    (f : A ⟶ X) [Nonempty X] (n : ℕ) :
    IsIso (mappingConeCollapseCollarHrelMap f n) := by
  let middleCollapse :
      TopCat.of (mappingConeUpper f ∩ mappingConeLower f :
        Set (topologicalMappingCone f)) ⟶
      TopCat.of (mappingConeUpper (toUnit A) ∩ mappingConeLower (toUnit A) :
        Set (topologicalMappingCone (toUnit A))) :=
    topologicalMappingConeCollapseMiddle f
  let upperCollapse := topologicalMappingConeCollapseUpper f
  haveI middleCollapseIso : IsIso middleCollapse := by
    apply (TopCat.isIso_iff_isHomeomorph middleCollapse).mpr
    simpa only [middleCollapse, mappingConeMiddle] using
      topologicalMappingConeCollapseMiddle_isHomeomorph f
  haveI upperCollapseIso : IsIso upperCollapse := by
    dsimp only [upperCollapse]
    exact topologicalMappingConeCollapseUpper_isIso f
  change IsIso (HrelMap n
    (mvInclLeft (mappingConeUpper f) (mappingConeLower f))
    (mvInclLeft (mappingConeUpper (toUnit A)) (mappingConeLower (toUnit A)))
    (show mvInclLeft (mappingConeUpper f) (mappingConeLower f) ≫
        topologicalMappingConeCollapseUpper f =
      topologicalMappingConeCollapseMiddle f ≫
        mvInclLeft (mappingConeUpper (toUnit A))
          (mappingConeLower (toUnit A)) by rfl))
  exact isIso_HrelMap_of_isIso n
    (mvInclLeft (mappingConeUpper f) (mappingConeLower f))
    (mvInclLeft (mappingConeUpper (toUnit A)) (mappingConeLower (toUnit A)))
    (fA := middleCollapse)
    (f := upperCollapse)
    (show mvInclLeft (mappingConeUpper f) (mappingConeLower f) ≫
        topologicalMappingConeCollapseUpper f =
      topologicalMappingConeCollapseMiddle f ≫
        mvInclLeft (mappingConeUpper (toUnit A))
          (mappingConeLower (toUnit A)) by rfl)

/-- Naturality of relative excision for the mapping-cone collapse and its collar
restrictions. -/
theorem mappingConeCollapse_excision_naturality
    (f : A ⟶ X) (n : ℕ) :
    mvExcisionHrelMap (mappingConeUpper f) (mappingConeLower f) n ≫
        mappingConeCollapseLowerHrelMap f n =
      mappingConeCollapseCollarHrelMap f n ≫
        mvExcisionHrelMap (mappingConeUpper (toUnit A))
          (mappingConeLower (toUnit A)) n := by
  unfold mvExcisionHrelMap mappingConeCollapseLowerHrelMap
    mappingConeCollapseCollarHrelMap
  rw [HrelMap_comp, HrelMap_comp]
  congr 1

/-- Relative excision promotes the collar homeomorphism to an isomorphism on the lower-pair
relative homology. -/
theorem isIso_mappingConeCollapseLowerHrelMap
    (f : A ⟶ X) [Nonempty X] (n : ℕ) :
    IsIso (mappingConeCollapseLowerHrelMap f n) := by
  letI : IsIso
      (mvExcisionHrelMap (mappingConeUpper f) (mappingConeLower f) n) :=
    isIso_mvExcisionHrelMap (mappingConeUpper f) (mappingConeLower f)
      (mappingConeCover_interior_union f) n
  letI : IsIso
      (mvExcisionHrelMap (mappingConeUpper (toUnit A))
        (mappingConeLower (toUnit A)) n) :=
    isIso_mvExcisionHrelMap (mappingConeUpper (toUnit A))
      (mappingConeLower (toUnit A))
      (mappingConeCover_interior_union (toUnit A)) n
  letI : IsIso (mappingConeCollapseCollarHrelMap f n) :=
    isIso_mappingConeCollapseCollarHrelMap f n
  exact IsIso.of_isIso_fac_left
    (mappingConeCollapse_excision_naturality f n)

/-- The relative-homology map of the canonical cofiber collapse. -/
def mappingConeCollapseHrelMap (f : A ⟶ X) (n : ℕ) :
    Hrel n (topologicalMappingConeIncl f) ⟶
      Hrel n (topologicalMappingConeIncl (toUnit A)) :=
  HrelMap n (topologicalMappingConeIncl f)
    (topologicalMappingConeIncl (toUnit A))
    (topologicalMappingConeIncl_collapseToMappingCone f)

/-- Replacing both original-space members by lower collars commutes with the relative map of
the cofiber collapse. -/
theorem mappingConeCollapse_lowerPair_naturality
    (f : A ⟶ X) (n : ℕ) :
    mappingConeCollapseHrelMap f n ≫
        mappingConeLowerPairHrelMap (toUnit A) n =
      mappingConeLowerPairHrelMap f n ≫
        mappingConeCollapseLowerHrelMap f n := by
  unfold mappingConeCollapseHrelMap mappingConeLowerPairHrelMap
    mappingConeCollapseLowerHrelMap
  rw [HrelMap_comp, HrelMap_comp]
  apply HrelMap_eq_of_maps_eq
  · exact (mappingConeLowerIncl_collapseLower f).symm
  · simp

/-- **Relative homology of a cofiber collapse.** If the original-space summand is nonempty,
collapsing it induces an isomorphism from the relative homology of the mapping-cone inclusion
to the relative homology of the distinguished suspension point. -/
theorem isIso_mappingConeCollapseHrelMap
    (f : A ⟶ X) [Nonempty X] (n : ℕ) :
    IsIso (mappingConeCollapseHrelMap f n) := by
  letI : Nonempty ((𝟙_ TopCat.{0} : TopCat.{0}) : Type) :=
    ⟨toUnit X (Classical.choice inferInstance)⟩
  letI : IsIso (mappingConeLowerPairHrelMap f n) :=
    isIso_mappingConeLowerPairHrelMap f n
  letI : IsIso (mappingConeLowerPairHrelMap (toUnit A) n) :=
    isIso_mappingConeLowerPairHrelMap (toUnit A) n
  letI : IsIso (mappingConeCollapseLowerHrelMap f n) :=
    isIso_mappingConeCollapseLowerHrelMap f n
  exact IsIso.of_isIso_fac_right
    (mappingConeCollapse_lowerPair_naturality f n)

end Submission
