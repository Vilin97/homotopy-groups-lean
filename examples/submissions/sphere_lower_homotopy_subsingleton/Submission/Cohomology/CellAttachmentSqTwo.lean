/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.SingularSqTwo
import Submission.Cohomology.Pair
import Submission.Topology.CellAttachment
import Submission.Topology.MappingCone

/-!
# A Steenrod-square obstruction for one-cell attachments

Naturality of the degree-three operation `Sq²` obstructs a retraction of an inclusion whenever a
degree-three class on the larger space is pulled back from the smaller space but has nonzero
square.  For a one-cell attachment, an extension of the attaching map across the disk would
produce exactly such a retraction.

This packages the formal obstruction needed for the mapping-cone proof that the suspended Hopf
map is non-null.  The remaining specialization must compute the two mod-two cohomology classes
and the nonzero value of `Sq²` on the Hopf attachment.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped TopCat

noncomputable section

namespace Submission

/-- A nonzero degree-three `Sq²` obstructs a retraction. -/
theorem not_exists_retraction_of_sqTwoDegreeThree
    {X C : TopCat.{0}} (i : X ⟶ C)
    (x : Hsing 3 X (ZMod 2)) (u : Hsing 3 C (ZMod 2))
    (hu : Hsing.map i 3 u = x)
    (hi : Function.Injective (Hsing.map (R := ZMod 2) i 3))
    (hx : sqTwoHsingDegreeThree x = 0)
    (huSq : sqTwoHsingDegreeThree u ≠ 0) :
    ¬ ∃ r : C ⟶ X, i ≫ r = 𝟙 X := by
  rintro ⟨r, hr⟩
  have hir : Hsing.map i 3 (Hsing.map r 3 x) = x := by
    rw [← LinearMap.comp_apply, ← Hsing.map_comp, hr, Hsing.map_id]
    rfl
  have hur : u = Hsing.map r 3 x :=
    hi (hu.trans hir.symm)
  apply huSq
  rw [hur, ← sqTwoHsingDegreeThree_natural, hx, map_zero]

/-- In the presence of the same `Sq²` data, the attaching map cannot extend across its disk. -/
theorem not_exists_cellAttachment_extension_of_sqTwoDegreeThree
    {X : TopCat.{0}} {n : ℕ} (a : TopCat.diskBoundary n ⟶ X)
    (x : Hsing 3 X (ZMod 2))
    (u : Hsing 3 (cellAttachment a) (ZMod 2))
    (hu : Hsing.map (cellAttachmentIncl a) 3 u = x)
    (hi : Function.Injective
      (Hsing.map (R := ZMod 2) (cellAttachmentIncl a) 3))
    (hx : sqTwoHsingDegreeThree x = 0)
    (huSq : sqTwoHsingDegreeThree u ≠ 0) :
    ¬ ∃ A : TopCat.disk n ⟶ X, TopCat.diskBoundaryIncl n ≫ A = a := by
  intro hA
  apply not_exists_retraction_of_sqTwoDegreeThree
    (cellAttachmentIncl a) x u hu hi hx huSq
  obtain ⟨A, hA⟩ := hA
  exact ⟨cellAttachmentRetractOfExtension a A hA,
    cellAttachmentIncl_retractOfExtension a A hA⟩

/-- The same square calculation detects that a map is not nullhomotopic from cohomology of its
mapping cone. -/
theorem not_exists_nullhomotopy_of_mappingCone_sqTwoDegreeThree
    {A X : TopCat.{0}} (f : A ⟶ X)
    (x : Hsing 3 X (ZMod 2))
    (u : Hsing 3 (topologicalMappingCone f) (ZMod 2))
    (hu : Hsing.map (topologicalMappingConeIncl f) 3 u = x)
    (hi : Function.Injective
      (Hsing.map (R := ZMod 2) (topologicalMappingConeIncl f) 3))
    (hx : sqTwoHsingDegreeThree x = 0)
    (huSq : sqTwoHsingDegreeThree u ≠ 0) :
    ¬ ∃ (p : 𝟙_ TopCat.{0} ⟶ X),
      Nonempty (TopCat.Homotopy f (toUnit A ≫ p)) := by
  intro hH
  apply not_exists_retraction_of_sqTwoDegreeThree
    (topologicalMappingConeIncl f) x u hu hi hx huSq
  obtain ⟨p, ⟨H⟩⟩ := hH
  exact ⟨topologicalMappingConeRetractOfNullhomotopy f p H,
    topologicalMappingConeIncl_retractOfNullhomotopy f p H⟩

/-- Relative vanishing in degrees three and four supplies the injectivity hypothesis in the
mapping-cone obstruction automatically. -/
theorem not_exists_nullhomotopy_of_mappingCone_sqTwoDegreeThree_of_relative_vanishing
    {A X : TopCat.{0}} (f : A ⟶ X)
    (x : Hsing 3 X (ZMod 2))
    (u : Hsing 3 (topologicalMappingCone f) (ZMod 2))
    (hu : Hsing.map (topologicalMappingConeIncl f) 3 u = x)
    (h₃ : IsZero (HrelCoh (topologicalMappingConeIncl f)
      (AddCommGrpCat.of (ZMod 2)) 3))
    (h₄ : IsZero (HrelCoh (topologicalMappingConeIncl f)
      (AddCommGrpCat.of (ZMod 2)) 4))
    (hx : sqTwoHsingDegreeThree x = 0)
    (huSq : sqTwoHsingDegreeThree u ≠ 0) :
    ¬ ∃ (p : 𝟙_ TopCat.{0} ⟶ X),
      Nonempty (TopCat.Homotopy f (toUnit A ≫ p)) :=
  not_exists_nullhomotopy_of_mappingCone_sqTwoDegreeThree f x u hu
    (bijective_Hsing_map_of_isZero_HrelCoh
      (topologicalMappingConeIncl f) (ZMod 2) 3 h₃ h₄).1 hx huSq

end Submission
