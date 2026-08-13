/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.Excision
import Submission.Cohomology.Point
import Submission.Cohomology.Sphere
import Submission.Topology.MappingConeCover

/-!
# Low-degree relative cohomology of a mapping cone

The standard height cover of a mapping cone has lower collar homotopy equivalent to the target,
contractible upper collar, and overlap homotopy equivalent to the attaching space.  Cohomological
excision therefore identifies the relative cohomology of the mapping-cone inclusion with the
shifted cohomology of the attaching space, in the vanishing range needed below.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

variable {A X : TopCat.{0}}
variable (R : Type) [CommRing R]

/-- Cohomology vanishing transfers from the attaching space to the middle mapping-cone collar. -/
theorem subsingleton_Hsing_mappingConeMiddle
    (f : A ⟶ X) [Nonempty A] (k : ℕ) [Subsingleton (Hsing k A R)] :
    Subsingleton (Hsing k (TopCat.of (mappingConeMiddle f)) R) := by
  have hstrict : mappingConeMiddleIncl f ≫ mappingConeMiddleRetract f = 𝟙 A := by
    ext a
    exact mappingConeMiddleRetract_incl f a
  let Hstrict : TopCat.Homotopy
      (mappingConeMiddleIncl f ≫ mappingConeMiddleRetract f) (𝟙 A) :=
    hstrict ▸ TopCat.Homotopy.refl (𝟙 A)
  let e : Hsing k A R ≃ₗ[R] Hsing k (TopCat.of (mappingConeMiddle f)) R :=
    hsingLinearEquivOfHomotopyEquiv
      (mappingConeMiddleRetract f) (mappingConeMiddleIncl f)
      (mappingConeMiddleDeformation f) Hstrict k
  exact ⟨fun a b ↦ e.symm.injective (Subsingleton.elim (e.symm a) (e.symm b))⟩

/-- If degree-`k` cohomology of the attaching space vanishes, then degree `k+1` relative
cohomology of the upper collar and its overlap vanishes. -/
theorem isZero_HrelCoh_mappingConeUpper_middle
    (f : A ⟶ X) [Nonempty A] (k : ℕ) [Subsingleton (Hsing k A R)] :
    IsZero (HrelCoh
      (mvInclLeft (mappingConeUpper f) (mappingConeLower f))
      (AddCommGrpCat.of R) (k + 1)) := by
  have hm : Subsingleton (Hsing k (TopCat.of
      (mappingConeUpper f ∩ mappingConeLower f : Set (topologicalMappingCone f))) R) := by
    change Subsingleton (Hsing k (TopCat.of (mappingConeMiddle f)) R)
    exact subsingleton_Hsing_mappingConeMiddle R f k
  letI := hm
  apply isZero_HrelCoh_of_isZero_subspace_of_isZero_space
    (mvInclLeft (mappingConeUpper f) (mappingConeLower f))
    (AddCommGrpCat.of R) k
  · exact isZero_dualHomology_of_subsingleton_Hsing R k
  · exact isZero_dualHomology_of_contractible R (k + 1) (by omega)

/-- Excision transfers upper-collar relative vanishing to the pair consisting of the whole
mapping cone and its lower collar. -/
theorem isZero_HrelCoh_mappingCone_lower
    (f : A ⟶ X) [Nonempty A] (k : ℕ) [Subsingleton (Hsing k A R)] :
    IsZero (HrelCoh (subIncl (mappingConeLower f))
      (AddCommGrpCat.of R) (k + 1)) := by
  have hcover : interior (mappingConeUpper f) ∪ interior (mappingConeLower f) =
      Set.univ := by
    rw [(isOpen_mappingConeUpper f).interior_eq,
      (isOpen_mappingConeLower f).interior_eq, mappingConeUpper_union_lower]
  letI : IsIso (mvExcisionHrelCohMap
      (mappingConeUpper f) (mappingConeLower f)
      (AddCommGrpCat.of R) (k + 1)) :=
    isIso_mvExcisionHrelCohMap
      (mappingConeUpper f) (mappingConeLower f)
      (AddCommGrpCat.of R) hcover k
  exact IsZero.of_iso (isZero_HrelCoh_mappingConeUpper_middle R f k)
    (asIso (mvExcisionHrelCohMap
      (mappingConeUpper f) (mappingConeLower f)
      (AddCommGrpCat.of R) (k + 1)))

/-- Replacing the original mapping-cone summand by its lower collar induces an isomorphism on
positive relative cohomology. -/
theorem isIso_mappingConeLower_pair_HrelCohMap
    (f : A ⟶ X) [Nonempty X] (k : ℕ) :
    IsIso (HrelCohMap (topologicalMappingConeIncl f) (AddCommGrpCat.of R)
      (subIncl (mappingConeLower f))
      (show topologicalMappingConeIncl f ≫ 𝟙 (topologicalMappingCone f) =
        mappingConeLowerIncl f ≫ subIncl (mappingConeLower f) by rfl)
      (k + 1)) := by
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
  apply isIso_HrelCohMap_of_homotopyEquiv
    (topologicalMappingConeIncl f) (AddCommGrpCat.of R)
    (subIncl (mappingConeLower f))
    (show topologicalMappingConeIncl f ≫ 𝟙 (topologicalMappingCone f) =
      mappingConeLowerIncl f ≫ subIncl (mappingConeLower f) by rfl)
    (mappingConeLowerRetract f) HA₁ (mappingConeLowerDeformation f)
    (𝟙 (topologicalMappingCone f)) HI HI k

/-- Vanishing of degree-`k` cohomology of the attaching space implies vanishing of degree
`k+1` relative cohomology of its mapping-cone inclusion. -/
theorem isZero_HrelCoh_mappingConeIncl_of_subsingleton_Hsing
    (f : A ⟶ X) [Nonempty A] (k : ℕ) [Subsingleton (Hsing k A R)] :
    IsZero (HrelCoh (topologicalMappingConeIncl f)
      (AddCommGrpCat.of R) (k + 1)) := by
  letI : Nonempty X := ⟨f (Classical.choice inferInstance)⟩
  let w : topologicalMappingConeIncl f ≫ 𝟙 (topologicalMappingCone f) =
      mappingConeLowerIncl f ≫ subIncl (mappingConeLower f) := by rfl
  letI : IsIso (HrelCohMap
      (topologicalMappingConeIncl f) (AddCommGrpCat.of R)
      (subIncl (mappingConeLower f)) w (k + 1)) :=
    isIso_mappingConeLower_pair_HrelCohMap R f k
  exact IsZero.of_iso (isZero_HrelCoh_mappingCone_lower R f k)
    (asIso (HrelCohMap
      (topologicalMappingConeIncl f) (AddCommGrpCat.of R)
      (subIncl (mappingConeLower f)) w (k + 1))).symm

/-- Mapping cones attached along a sphere have the expected low-degree relative-cohomology
vanishing. -/
theorem isZero_HrelCoh_mappingConeIncl_sphere
    (n : ℕ) (f : TopCat.of (Sph n) ⟶ X) (k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n) :
    IsZero (HrelCoh (topologicalMappingConeIncl f)
      (AddCommGrpCat.of R) (k + 1)) := by
  letI : Subsingleton (Hsing k (TopCat.of (Sph n)) R) :=
    subsingleton_Hsing_sphere R k n hk hkn
  exact isZero_HrelCoh_mappingConeIncl_of_subsingleton_Hsing R f k

end Submission
