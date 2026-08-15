/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneProjectiveLineRelativeHomologyClassification
import Submission.ComplexProjectivePlanePuppe

/-!
# The cofiber of the embedded projective line

The four-cell presentation of geometric `CP²` has a canonical collapse to `S⁴`.  This file
computes its fibres exactly: two points have the same image precisely when they are equal or
both lie in the bottom projective line.  It follows that the literal quotient obtained by
collapsing `CP¹` inside `CP²` is homeomorphic to the metric four-sphere.
-/

open CategoryTheory
open scoped Topology TopCat

noncomputable section

namespace Submission

/-! ## Fibres of the collapse in the cell model -/

/-- The bottom projective line inside the four-cell presentation of `CP²`. -/
def complexProjectivePlaneCellBottom : Set complexProjectivePlaneCell :=
  Set.range (cellAttachmentIncl diskBoundaryFourComplexHopfMap)

@[simp]
theorem complexProjectivePlaneCellCollapse_incl_apply
    (p : ComplexProjectiveModel 1) :
    complexProjectivePlaneCellCollapse
        (cellAttachmentIncl diskBoundaryFourComplexHopfMap p) =
      sphereBasepoint 4 :=
  ConcreteCategory.congr_hom complexProjectivePlaneCellCollapse_incl p

@[simp]
theorem complexProjectivePlaneCellCollapse_disk_apply
    (x : TopCat.disk.{0} 4) :
    complexProjectivePlaneCellCollapse
        (cellAttachmentDisk diskBoundaryFourComplexHopfMap x) =
      diskToSphere 4 x :=
  ConcreteCategory.congr_hom complexProjectivePlaneCellCollapse_disk x

/-- A boundary point of the attached four-disk already lies in the bottom projective-line
summand. -/
theorem complexProjectivePlaneCellDisk_mem_bottom_of_norm_eq_one
    (x : TopCat.disk.{0} 4) (hx : ‖x.down.val‖ = 1) :
    cellAttachmentDisk diskBoundaryFourComplexHopfMap x ∈
      complexProjectivePlaneCellBottom := by
  let z : TopCat.diskBoundary.{0} 4 :=
    ULift.up ⟨x.down.val, mem_sphere_zero_iff_norm.mpr hx⟩
  have hz : TopCat.diskBoundaryIncl 4 z = x := by
    apply ULift.ext
    apply Subtype.ext
    rfl
  refine ⟨diskBoundaryFourComplexHopfMap z, ?_⟩
  have hc := ConcreteCategory.congr_hom
    (cellAttachment_condition diskBoundaryFourComplexHopfMap) z
  change cellAttachmentIncl diskBoundaryFourComplexHopfMap
      (diskBoundaryFourComplexHopfMap z) =
    cellAttachmentDisk diskBoundaryFourComplexHopfMap
      (TopCat.diskBoundaryIncl 4 z) at hc
  rwa [hz] at hc

/-- The cell collapse identifies exactly the bottom projective-line summand and no other
points. -/
theorem complexProjectivePlaneCellCollapse_eq_iff
    (p q : complexProjectivePlaneCell) :
    complexProjectivePlaneCellCollapse p =
        complexProjectivePlaneCellCollapse q ↔
      p = q ∨
        (p ∈ complexProjectivePlaneCellBottom ∧
          q ∈ complexProjectivePlaneCellBottom) := by
  constructor
  · intro h
    obtain ⟨sp, rfl⟩ :=
      (pushoutSumDesc_isQuotientMap diskBoundaryFourComplexHopfMap
        (TopCat.diskBoundaryIncl 4)).surjective p
    obtain ⟨sq, rfl⟩ :=
      (pushoutSumDesc_isQuotientMap diskBoundaryFourComplexHopfMap
        (TopCat.diskBoundaryIncl 4)).surjective q
    rcases sp with x | x <;> rcases sq with y | y
    · right
      exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
    · right
      refine ⟨⟨x, rfl⟩, ?_⟩
      apply complexProjectivePlaneCellDisk_mem_bottom_of_norm_eq_one
      apply (diskToSphereFour_eq_basepoint_iff y).mp
      change complexProjectivePlaneCellCollapse
          (cellAttachmentIncl diskBoundaryFourComplexHopfMap x) =
        complexProjectivePlaneCellCollapse
          (cellAttachmentDisk diskBoundaryFourComplexHopfMap y) at h
      rw [complexProjectivePlaneCellCollapse_incl_apply,
        complexProjectivePlaneCellCollapse_disk_apply] at h
      exact h.symm
    · right
      refine ⟨?_, ⟨y, rfl⟩⟩
      apply complexProjectivePlaneCellDisk_mem_bottom_of_norm_eq_one
      apply (diskToSphereFour_eq_basepoint_iff x).mp
      change complexProjectivePlaneCellCollapse
          (cellAttachmentDisk diskBoundaryFourComplexHopfMap x) =
        complexProjectivePlaneCellCollapse
          (cellAttachmentIncl diskBoundaryFourComplexHopfMap y) at h
      rw [complexProjectivePlaneCellCollapse_disk_apply,
        complexProjectivePlaneCellCollapse_incl_apply] at h
      exact h
    · have hxy : diskToSphere 4 x = diskToSphere 4 y := by
        change complexProjectivePlaneCellCollapse
            (cellAttachmentDisk diskBoundaryFourComplexHopfMap x) =
          complexProjectivePlaneCellCollapse
            (cellAttachmentDisk diskBoundaryFourComplexHopfMap y) at h
        rwa [complexProjectivePlaneCellCollapse_disk_apply,
          complexProjectivePlaneCellCollapse_disk_apply] at h
      rcases (diskToSphereFour_eq_iff x y).mp hxy with hxy | ⟨hx, hy⟩
      · subst y
        exact Or.inl rfl
      · right
        exact
          ⟨complexProjectivePlaneCellDisk_mem_bottom_of_norm_eq_one x hx,
            complexProjectivePlaneCellDisk_mem_bottom_of_norm_eq_one y hy⟩
  · rintro (rfl | ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩)
    · rfl
    · rw [complexProjectivePlaneCellCollapse_incl_apply,
        complexProjectivePlaneCellCollapse_incl_apply]

/-- The collapse from the four-cell model onto `S⁴` is surjective. -/
theorem complexProjectivePlaneCellCollapse_surjective :
    Function.Surjective complexProjectivePlaneCellCollapse := by
  intro y
  obtain ⟨x, rfl⟩ := diskToSphere_surjective 3 y
  exact
    ⟨cellAttachmentDisk diskBoundaryFourComplexHopfMap x,
      complexProjectivePlaneCellCollapse_disk_apply x⟩

/-! ## The literal quotient of geometric `CP²` -/

/-- Collapse the literal bottom projective line in geometric `CP²` to the basepoint of
`S⁴`. -/
noncomputable def complexProjectivePlaneProjectiveLineCollapse :
    TopCat.of (ComplexProjectiveModel 2) ⟶ TopCat.of (Sph 4) :=
  (TopCat.isoOfHomeo complexProjectivePlaneCellHomeomorph).inv ≫
    complexProjectivePlaneCellCollapse

/-- The cell-model bottom summand corresponds exactly to the literal projective-line subtype
of geometric `CP²`. -/
theorem complexProjectivePlaneCellHomeomorph_mem_projectiveLine_iff
    (p : complexProjectivePlaneCell) :
    complexProjectivePlaneCellHomeomorph p ∈
        complexProjectivePlaneProjectiveLine ↔
      p ∈ complexProjectivePlaneCellBottom := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply complexProjectivePlaneCellHomeomorph.injective
    rw [complexProjectivePlaneCellHomeomorph_incl]
    change complexProjectivePlaneBottomIncl x =
      complexProjectivePlaneCellHomeomorph p at hx
    exact hx
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    change complexProjectivePlaneBottomIncl x =
      complexProjectivePlaneCellHomeomorph
        (cellAttachmentIncl diskBoundaryFourComplexHopfMap x)
    exact (complexProjectivePlaneCellHomeomorph_incl x).symm

/-- The geometric collapse identifies precisely equal points and pairs of points both lying in
the literal projective line. -/
theorem complexProjectivePlaneProjectiveLineCollapse_eq_iff
    (x y : ComplexProjectiveModel 2) :
    complexProjectivePlaneProjectiveLineCollapse x =
        complexProjectivePlaneProjectiveLineCollapse y ↔
      x = y ∨
        (x ∈ complexProjectivePlaneProjectiveLine ∧
          y ∈ complexProjectivePlaneProjectiveLine) := by
  change complexProjectivePlaneCellCollapse
      (complexProjectivePlaneCellHomeomorph.symm x) =
        complexProjectivePlaneCellCollapse
          (complexProjectivePlaneCellHomeomorph.symm y) ↔ _
  rw [complexProjectivePlaneCellCollapse_eq_iff]
  constructor
  · rintro (hxy | ⟨hx, hy⟩)
    · exact Or.inl
        (complexProjectivePlaneCellHomeomorph.symm.injective hxy)
    · right
      constructor
      · simpa using
          (complexProjectivePlaneCellHomeomorph_mem_projectiveLine_iff
            (complexProjectivePlaneCellHomeomorph.symm x)).mpr hx
      · simpa using
          (complexProjectivePlaneCellHomeomorph_mem_projectiveLine_iff
            (complexProjectivePlaneCellHomeomorph.symm y)).mpr hy
  · rintro (hxy | ⟨hx, hy⟩)
    · exact Or.inl (congrArg complexProjectivePlaneCellHomeomorph.symm hxy)
    · right
      constructor
      · exact
          (complexProjectivePlaneCellHomeomorph_mem_projectiveLine_iff
            (complexProjectivePlaneCellHomeomorph.symm x)).mp (by simpa using hx)
      · exact
          (complexProjectivePlaneCellHomeomorph_mem_projectiveLine_iff
            (complexProjectivePlaneCellHomeomorph.symm y)).mp (by simpa using hy)

/-- The geometric projective-line collapse is surjective. -/
theorem complexProjectivePlaneProjectiveLineCollapse_surjective :
    Function.Surjective complexProjectivePlaneProjectiveLineCollapse := by
  intro y
  obtain ⟨p, hp⟩ := complexProjectivePlaneCellCollapse_surjective y
  refine ⟨complexProjectivePlaneCellHomeomorph p, ?_⟩
  change complexProjectivePlaneCellCollapse
      (complexProjectivePlaneCellHomeomorph.symm
        (complexProjectivePlaneCellHomeomorph p)) = y
  rw [complexProjectivePlaneCellHomeomorph.symm_apply_apply]
  exact hp

/-- The geometric projective-line collapse is a quotient map. -/
theorem complexProjectivePlaneProjectiveLineCollapse_isQuotientMap :
    Topology.IsQuotientMap complexProjectivePlaneProjectiveLineCollapse :=
  Topology.IsQuotientMap.of_surjective_continuous
    complexProjectivePlaneProjectiveLineCollapse_surjective
    complexProjectivePlaneProjectiveLineCollapse.hom.continuous

/-- The setoid that collapses the literal projective line and otherwise keeps points
distinct. -/
def complexProjectivePlaneProjectiveLineSetoid :
    Setoid (ComplexProjectiveModel 2) where
  r x y :=
    x = y ∨
      (x ∈ complexProjectivePlaneProjectiveLine ∧
        y ∈ complexProjectivePlaneProjectiveLine)
  iseqv := {
    refl := fun _ ↦ Or.inl rfl
    symm := by
      rintro x y (rfl | ⟨hx, hy⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨hy, hx⟩
    trans := by
      intro x y z hxy hyz
      rcases hxy with rfl | ⟨hx, hy⟩
      · exact hyz
      rcases hyz with rfl | ⟨hy', hz⟩
      · exact Or.inr ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hz⟩
  }

/-- The literal projective-line collapse setoid is exactly the kernel relation of the
geometric collapse map. -/
theorem complexProjectivePlaneProjectiveLineSetoid_eq_ker :
    complexProjectivePlaneProjectiveLineSetoid =
      Setoid.ker complexProjectivePlaneProjectiveLineCollapse := by
  apply Setoid.ext
  intro x y
  exact (complexProjectivePlaneProjectiveLineCollapse_eq_iff x y).symm

/-- Collapsing the literal embedded `CP¹` in geometric `CP²` gives the metric four-sphere. -/
noncomputable def complexProjectivePlaneQuotientProjectiveLineHomeomorphSphereFour :
    Quotient complexProjectivePlaneProjectiveLineSetoid ≃ₜ Sph 4 := by
  rw [complexProjectivePlaneProjectiveLineSetoid_eq_ker]
  exact complexProjectivePlaneProjectiveLineCollapse_isQuotientMap.homeomorph

end Submission
