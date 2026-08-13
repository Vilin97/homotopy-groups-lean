/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.Pair
import Submission.Topology.CellAttachment
import Submission.Topology.MappingCone

/-!
# A cup-square obstruction for one-cell attachments

Naturality of the degree-two cup square obstructs a retraction whenever a degree-two class on
the larger space restricts to a class with zero square but has nonzero square itself.  An
extension of a cell's attaching map, or a nullhomotopy of a mapping-cone map, would supply such a
retraction.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped TopCat

noncomputable section

namespace Submission

/-- A nonzero degree-two cup square obstructs a retraction. -/
theorem not_exists_retraction_of_cupSquareDegreeTwo
    {X C : TopCat.{0}} (i : X ⟶ C)
    (x : Hsing 2 X (ZMod 2)) (u : Hsing 2 C (ZMod 2))
    (hu : Hsing.map i 2 u = x)
    (hi : Function.Injective (Hsing.map (R := ZMod 2) i 2))
    (hx : cupHsing (by omega : 2 + 2 = 4) x x = 0)
    (huSq : cupHsing (by omega : 2 + 2 = 4) u u ≠ 0) :
    ¬ ∃ r : C ⟶ X, i ≫ r = 𝟙 X := by
  rintro ⟨r, hr⟩
  have hir : Hsing.map i 2 (Hsing.map r 2 x) = x := by
    rw [← LinearMap.comp_apply, ← Hsing.map_comp, hr, Hsing.map_id]
    rfl
  have hur : u = Hsing.map r 2 x := hi (hu.trans hir.symm)
  apply huSq
  rw [hur, ← map_cupHsing, hx, map_zero]

/-- In the presence of the same cup-square data, the attaching map cannot extend across its
disk. -/
theorem not_exists_cellAttachment_extension_of_cupSquareDegreeTwo
    {X : TopCat.{0}} {n : ℕ} (a : TopCat.diskBoundary n ⟶ X)
    (x : Hsing 2 X (ZMod 2))
    (u : Hsing 2 (cellAttachment a) (ZMod 2))
    (hu : Hsing.map (cellAttachmentIncl a) 2 u = x)
    (hi : Function.Injective
      (Hsing.map (R := ZMod 2) (cellAttachmentIncl a) 2))
    (hx : cupHsing (by omega : 2 + 2 = 4) x x = 0)
    (huSq : cupHsing (by omega : 2 + 2 = 4) u u ≠ 0) :
    ¬ ∃ A : TopCat.disk n ⟶ X, TopCat.diskBoundaryIncl n ≫ A = a := by
  intro hA
  apply not_exists_retraction_of_cupSquareDegreeTwo
    (cellAttachmentIncl a) x u hu hi hx huSq
  obtain ⟨A, hA⟩ := hA
  exact ⟨cellAttachmentRetractOfExtension a A hA,
    cellAttachmentIncl_retractOfExtension a A hA⟩

/-- A nonzero cup square on a mapping cone detects that its attaching map is not nullhomotopic. -/
theorem not_exists_nullhomotopy_of_mappingCone_cupSquareDegreeTwo
    {A X : TopCat.{0}} (f : A ⟶ X)
    (x : Hsing 2 X (ZMod 2))
    (u : Hsing 2 (topologicalMappingCone f) (ZMod 2))
    (hu : Hsing.map (topologicalMappingConeIncl f) 2 u = x)
    (hi : Function.Injective
      (Hsing.map (R := ZMod 2) (topologicalMappingConeIncl f) 2))
    (hx : cupHsing (by omega : 2 + 2 = 4) x x = 0)
    (huSq : cupHsing (by omega : 2 + 2 = 4) u u ≠ 0) :
    ¬ ∃ (p : 𝟙_ TopCat.{0} ⟶ X),
      Nonempty (TopCat.Homotopy f (toUnit A ≫ p)) := by
  intro hH
  apply not_exists_retraction_of_cupSquareDegreeTwo
    (topologicalMappingConeIncl f) x u hu hi hx huSq
  obtain ⟨p, ⟨H⟩⟩ := hH
  exact ⟨topologicalMappingConeRetractOfNullhomotopy f p H,
    topologicalMappingConeIncl_retractOfNullhomotopy f p H⟩

end Submission
