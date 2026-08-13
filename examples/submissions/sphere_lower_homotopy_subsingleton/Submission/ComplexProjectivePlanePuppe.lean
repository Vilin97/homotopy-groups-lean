/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneCell
import Submission.Topology.MappingCone

/-!
# The cone-disk model for the projective-plane Puppe sequence

This file begins the point-set comparison between the mapping cone of the exact Hopf attaching
map and the four-cell model of complex projective two-space.  Its first ingredient is the
explicit radial homeomorphism from the cone on `∂D⁴` to `D⁴`.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology TopCat

noncomputable section

namespace Submission

/-- Send `(z, t)` in the cone cylinder on `∂D⁴` to `(1 - t) z` in `D⁴`. -/
noncomputable def diskBoundaryFourConeCylinderToDisk
    (p : TopCat.diskBoundary.{0} 4 × TopCat.I.{0}) : TopCat.disk.{0} 4 :=
  ULift.up ⟨(1 - (TopCat.I.homeomorph p.2 : ℝ)) • p.1.down.val, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg]
    · rw [mem_sphere_zero_iff_norm.mp p.1.down.property, mul_one]
      exact sub_le_self 1 (TopCat.I.homeomorph p.2).property.1
    · exact sub_nonneg.mpr (TopCat.I.homeomorph p.2).property.2⟩

theorem continuous_diskBoundaryFourConeCylinderToDisk :
    Continuous diskBoundaryFourConeCylinderToDisk := by
  apply continuous_uliftUp.comp
  apply Continuous.subtype_mk
  fun_prop

noncomputable def diskBoundaryFourConeCylinderToDiskTopCat :
    TopCat.diskBoundary.{0} 4 ⊗ TopCat.I.{0} ⟶ TopCat.disk.{0} 4 :=
  TopCat.ofHom ⟨diskBoundaryFourConeCylinderToDisk,
    continuous_diskBoundaryFourConeCylinderToDisk⟩

noncomputable def diskFourCenter : TopCat.disk.{0} 4 :=
  ULift.up ⟨0, by simp⟩

/-- The radial cylinder map descends to the cone because its top is the disk center. -/
noncomputable def diskBoundaryFourConeToDisk :
    topologicalCone (TopCat.diskBoundary.{0} 4) ⟶ TopCat.disk.{0} 4 :=
  topologicalConeDesc (TopCat.diskBoundary 4)
    diskBoundaryFourConeCylinderToDiskTopCat
    (TopCat.const diskFourCenter)
    (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      apply ULift.ext
      apply Subtype.ext
      change (1 - (TopCat.I.homeomorph (1 : TopCat.I.{0}) : ℝ)) •
        z.down.val = 0
      apply smul_eq_zero.mpr
      left
      rw [TopCat.I.homeomorph_one]
      norm_num)

@[simp]
theorem diskBoundaryFourConeToDisk_cylinder
    (z : TopCat.diskBoundary.{0} 4) (t : TopCat.I.{0}) :
    diskBoundaryFourConeToDisk
        (topologicalConeCylinderIncl (TopCat.diskBoundary 4) (z, t)) =
      diskBoundaryFourConeCylinderToDisk (z, t) := by
  exact ConcreteCategory.congr_hom
    (topologicalConeCylinderIncl_desc (TopCat.diskBoundary 4)
      diskBoundaryFourConeCylinderToDiskTopCat
      (TopCat.const diskFourCenter) _) (z, t)

@[simp]
theorem diskBoundaryFourConeToDisk_point (u : PUnit) :
    diskBoundaryFourConeToDisk
        (topologicalConePointIncl (TopCat.diskBoundary 4) u) =
      diskFourCenter := by
  exact ConcreteCategory.congr_hom
    (topologicalConePointIncl_desc (TopCat.diskBoundary 4)
      diskBoundaryFourConeCylinderToDiskTopCat
      (TopCat.const diskFourCenter) _) u

theorem diskBoundaryFourConeCylinderToDisk_surjective :
    Function.Surjective diskBoundaryFourConeCylinderToDisk := by
  intro x
  by_cases hx : ‖x.down.val‖ = 0
  · let z : TopCat.diskBoundary.{0} 4 :=
      ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩
    refine ⟨(z, (1 : TopCat.I.{0})), ?_⟩
    apply ULift.ext
    apply Subtype.ext
    change (1 - (TopCat.I.homeomorph (1 : TopCat.I.{0}) : ℝ)) •
      z.down.val = x.down.val
    rw [TopCat.I.homeomorph_one]
    have hxzero : x.down.val = 0 := norm_eq_zero.mp hx
    simp [hxzero]
  · have hxpos : 0 < ‖x.down.val‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    have hxle : ‖x.down.val‖ ≤ 1 := by
      have := x.down.property
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this
    let z : TopCat.diskBoundary.{0} 4 := ULift.up
      ⟨‖x.down.val‖⁻¹ • x.down.val, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_inv, abs_norm, inv_mul_cancel₀ (ne_of_gt hxpos)]⟩
    let t : TopCat.I.{0} := TopCat.I.homeomorph.symm
      ⟨1 - ‖x.down.val‖, ⟨sub_nonneg.mpr hxle, sub_le_self 1 (norm_nonneg _)⟩⟩
    refine ⟨(z, t), ?_⟩
    apply ULift.ext
    apply Subtype.ext
    change (1 - (TopCat.I.homeomorph t : ℝ)) • z.down.val = x.down.val
    rw [TopCat.I.homeomorph.apply_symm_apply]
    change (1 - (1 - ‖x.down.val‖)) •
      (‖x.down.val‖⁻¹ • x.down.val) = x.down.val
    rw [sub_sub_cancel, smul_smul, mul_inv_cancel₀ (ne_of_gt hxpos), one_smul]

/-- The cone on the compact boundary of the four-disk is compact. -/
noncomputable instance diskBoundaryFourConeCompactSpace :
    CompactSpace (topologicalCone (TopCat.diskBoundary.{0} 4)) := by
  letI : CompactSpace TopCat.I.{0} :=
    TopCat.I.homeomorph.symm.compactSpace
  letI : CompactSpace
      ((TopCat.diskBoundary.{0} 4 ⊗ TopCat.I.{0} : TopCat.{0}) : Type) := by
    change CompactSpace ((TopCat.diskBoundary.{0} 4 : Type) × TopCat.I.{0})
    infer_instance
  letI : CompactSpace
      (((TopCat.diskBoundary.{0} 4 ⊗ TopCat.I.{0} : TopCat.{0}) : Type) ⊕
        ((𝟙_ TopCat.{0} : TopCat.{0}) : Type)) := by
    change CompactSpace
      (((TopCat.diskBoundary.{0} 4 : Type) × TopCat.I.{0}) ⊕ PUnit)
    infer_instance
  exact Function.Surjective.compactSpace
    (topologicalConeSumDesc_isQuotientMap
      (TopCat.diskBoundary 4)).continuous
    (topologicalConeSumDesc_isQuotientMap
      (TopCat.diskBoundary 4)).surjective

theorem diskBoundaryFourConeToDisk_surjective :
    Function.Surjective diskBoundaryFourConeToDisk := by
  intro x
  obtain ⟨c, rfl⟩ := diskBoundaryFourConeCylinderToDisk_surjective x
  exact ⟨topologicalConeCylinderIncl (TopCat.diskBoundary 4) c,
    diskBoundaryFourConeToDisk_cylinder c.1 c.2⟩

theorem diskBoundaryFourConeCylinderIncl_eq_point_of_radial_eq_center
    (c : TopCat.diskBoundary.{0} 4 × TopCat.I.{0})
    (h : diskBoundaryFourConeCylinderToDisk c = diskFourCenter) :
    topologicalConeCylinderIncl (TopCat.diskBoundary 4) c =
      topologicalConePointIncl (TopCat.diskBoundary 4) PUnit.unit := by
  have hvec := congrArg (fun x : TopCat.disk.{0} 4 ↦ x.down.val) h
  change (1 - (TopCat.I.homeomorph c.2 : ℝ)) • c.1.down.val = 0 at hvec
  have hzNorm : ‖c.1.down.val‖ = 1 :=
    mem_sphere_zero_iff_norm.mp c.1.down.property
  have hz : c.1.down.val ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hzNorm
    norm_num at hzNorm
  have hcoef : 1 - (TopCat.I.homeomorph c.2 : ℝ) = 0 :=
    (smul_eq_zero.mp hvec).resolve_right hz
  have htReal : (TopCat.I.homeomorph c.2 : ℝ) = 1 := by
    linarith
  have ht : c.2 = 1 := by
    apply TopCat.I.homeomorph.injective
    apply Subtype.ext
    simpa using htReal
  have htop :
      (TopCat.ι₁ : TopCat.diskBoundary.{0} 4 ⟶
        TopCat.diskBoundary.{0} 4 ⊗ TopCat.I.{0}) ≫
          topologicalConeCylinderIncl (TopCat.diskBoundary 4) =
        toUnit (TopCat.diskBoundary 4) ≫
          topologicalConePointIncl (TopCat.diskBoundary 4) :=
    pushout.condition
  have hc : c = (c.1, (1 : TopCat.I.{0})) := by
    apply Prod.ext
    · rfl
    · exact ht
  rw [hc]
  change (topologicalConeCylinderIncl (TopCat.diskBoundary 4)).hom
      (c.1, (1 : TopCat.I.{0})) =
    (topologicalConePointIncl (TopCat.diskBoundary 4)).hom PUnit.unit
  convert ConcreteCategory.congr_hom htop c.1 using 1 <;> rfl

theorem diskBoundaryFourConeCylinderToDisk_eq_imp_of_ne_center
    (c d : TopCat.diskBoundary.{0} 4 × TopCat.I.{0})
    (h : diskBoundaryFourConeCylinderToDisk c =
      diskBoundaryFourConeCylinderToDisk d)
    (hc : diskBoundaryFourConeCylinderToDisk c ≠ diskFourCenter) :
    c = d := by
  have hvec := congrArg (fun x : TopCat.disk.{0} 4 ↦ x.down.val) h
  change (1 - (TopCat.I.homeomorph c.2 : ℝ)) • c.1.down.val =
    (1 - (TopCat.I.homeomorph d.2 : ℝ)) • d.1.down.val at hvec
  have hcNonneg : 0 ≤ 1 - (TopCat.I.homeomorph c.2 : ℝ) :=
    sub_nonneg.mpr (TopCat.I.homeomorph c.2).property.2
  have hdNonneg : 0 ≤ 1 - (TopCat.I.homeomorph d.2 : ℝ) :=
    sub_nonneg.mpr (TopCat.I.homeomorph d.2).property.2
  have hcNorm : ‖c.1.down.val‖ = 1 :=
    mem_sphere_zero_iff_norm.mp c.1.down.property
  have hdNorm : ‖d.1.down.val‖ = 1 :=
    mem_sphere_zero_iff_norm.mp d.1.down.property
  have hnorm := congrArg norm hvec
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hcNonneg, abs_of_nonneg hdNonneg, hcNorm, hdNorm,
    mul_one, mul_one] at hnorm
  have hreal : (TopCat.I.homeomorph c.2 : ℝ) =
      (TopCat.I.homeomorph d.2 : ℝ) := by
    linarith
  have ht : c.2 = d.2 := by
    apply TopCat.I.homeomorph.injective
    apply Subtype.ext
    exact hreal
  have hcoef : 1 - (TopCat.I.homeomorph c.2 : ℝ) ≠ 0 := by
    intro hzero
    apply hc
    apply ULift.ext
    apply Subtype.ext
    change (1 - (TopCat.I.homeomorph c.2 : ℝ)) • c.1.down.val = 0
    rw [hzero, zero_smul]
  have hs : (1 - (TopCat.I.homeomorph c.2 : ℝ)) • c.1.down.val =
      (1 - (TopCat.I.homeomorph c.2 : ℝ)) • d.1.down.val := by
    simpa [hreal] using hvec
  have hzvec : c.1.down.val = d.1.down.val :=
    smul_right_injective _ hcoef hs
  have hz : c.1 = d.1 := by
    apply ULift.ext
    apply Subtype.ext
    exact hzvec
  exact Prod.ext hz ht

@[simp]
theorem topologicalConeSumDesc_diskBoundaryFour_inl
    (c : TopCat.diskBoundary.{0} 4 × TopCat.I.{0}) :
    topologicalConeSumDesc (TopCat.diskBoundary 4) (Sum.inl c) =
      topologicalConeCylinderIncl (TopCat.diskBoundary 4) c :=
  rfl

@[simp]
theorem topologicalConeSumDesc_diskBoundaryFour_inr
    (u : (𝟙_ TopCat.{0} : TopCat.{0})) :
    topologicalConeSumDesc (TopCat.diskBoundary 4) (Sum.inr u) =
      topologicalConePointIncl (TopCat.diskBoundary 4) u :=
  rfl

@[simp]
theorem diskBoundaryFourConeToDisk_cylinder_pair
    (c : TopCat.diskBoundary.{0} 4 × TopCat.I.{0}) :
    diskBoundaryFourConeToDisk
        (topologicalConeCylinderIncl (TopCat.diskBoundary 4) c) =
      diskBoundaryFourConeCylinderToDisk c := by
  rcases c with ⟨z, t⟩
  exact diskBoundaryFourConeToDisk_cylinder z t

theorem diskBoundaryFourConeToDisk_injective :
    Function.Injective diskBoundaryFourConeToDisk := by
  intro x y h
  obtain ⟨sx, rfl⟩ :=
    (topologicalConeSumDesc_isQuotientMap
      (TopCat.diskBoundary 4)).surjective x
  obtain ⟨sy, rfl⟩ :=
    (topologicalConeSumDesc_isQuotientMap
      (TopCat.diskBoundary 4)).surjective y
  rcases sx with c | u <;> rcases sy with d | v
  · have hrad : diskBoundaryFourConeCylinderToDisk c =
        diskBoundaryFourConeCylinderToDisk d := by
      simpa only [topologicalConeSumDesc_diskBoundaryFour_inl,
        diskBoundaryFourConeToDisk_cylinder_pair] using h
    by_cases hc : diskBoundaryFourConeCylinderToDisk c = diskFourCenter
    · have hd : diskBoundaryFourConeCylinderToDisk d = diskFourCenter :=
        hrad.symm.trans hc
      exact
        (diskBoundaryFourConeCylinderIncl_eq_point_of_radial_eq_center c hc).trans
          (diskBoundaryFourConeCylinderIncl_eq_point_of_radial_eq_center d hd).symm
    · have hcd :=
        diskBoundaryFourConeCylinderToDisk_eq_imp_of_ne_center c d hrad hc
      subst d
      rfl
  · have hrad : diskBoundaryFourConeCylinderToDisk c =
        diskFourCenter := by
      simpa only [topologicalConeSumDesc_diskBoundaryFour_inl,
        topologicalConeSumDesc_diskBoundaryFour_inr,
        diskBoundaryFourConeToDisk_cylinder_pair,
        diskBoundaryFourConeToDisk_point] using h
    change PUnit at v
    cases v
    exact diskBoundaryFourConeCylinderIncl_eq_point_of_radial_eq_center c hrad
  · have hrad : diskFourCenter =
        diskBoundaryFourConeCylinderToDisk d := by
      simpa only [topologicalConeSumDesc_diskBoundaryFour_inl,
        topologicalConeSumDesc_diskBoundaryFour_inr,
        diskBoundaryFourConeToDisk_cylinder_pair,
        diskBoundaryFourConeToDisk_point] using h
    change PUnit at u
    cases u
    exact (diskBoundaryFourConeCylinderIncl_eq_point_of_radial_eq_center d hrad.symm).symm
  · change PUnit at u v
    cases u
    cases v
    rfl

/-- The cone on the boundary of the four-disk is radially homeomorphic to the four-disk. -/
noncomputable def diskBoundaryFourConeHomeomorphDisk :
    topologicalCone (TopCat.diskBoundary.{0} 4) ≃ₜ TopCat.disk.{0} 4 := by
  letI : T2Space (TopCat.disk.{0} 4) := by
    unfold TopCat.disk
    infer_instance
  exact IsHomeomorph.homeomorph diskBoundaryFourConeToDisk <|
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨diskBoundaryFourConeToDisk.hom.continuous,
        diskBoundaryFourConeToDisk_injective,
        diskBoundaryFourConeToDisk_surjective⟩

@[simp]
theorem diskBoundaryFourConeHomeomorphDisk_cylinder
    (c : TopCat.diskBoundary.{0} 4 × TopCat.I.{0}) :
    diskBoundaryFourConeHomeomorphDisk
        (topologicalConeCylinderIncl (TopCat.diskBoundary 4) c) =
      diskBoundaryFourConeCylinderToDisk c := by
  change diskBoundaryFourConeToDisk
      (topologicalConeCylinderIncl (TopCat.diskBoundary 4) c) = _
  exact diskBoundaryFourConeToDisk_cylinder_pair c

@[simp]
theorem diskBoundaryFourConeHomeomorphDisk_point (u : PUnit) :
    diskBoundaryFourConeHomeomorphDisk
        (topologicalConePointIncl (TopCat.diskBoundary 4) u) =
      diskFourCenter := by
  change diskBoundaryFourConeToDisk
      (topologicalConePointIncl (TopCat.diskBoundary 4) u) = _
  exact diskBoundaryFourConeToDisk_point u

/-! ## Comparison of the Hopf mapping cone and cell attachment -/

noncomputable def diskBoundaryFourConeIsoDisk :
    topologicalCone (TopCat.diskBoundary.{0} 4) ≅ TopCat.disk.{0} 4 :=
  TopCat.isoOfHomeo diskBoundaryFourConeHomeomorphDisk

@[reassoc]
theorem diskBoundaryFourConeBaseIncl_isoDisk :
    topologicalConeBaseIncl (TopCat.diskBoundary.{0} 4) ≫
        diskBoundaryFourConeIsoDisk.hom =
      TopCat.diskBoundaryIncl 4 := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change diskBoundaryFourConeHomeomorphDisk
      (topologicalConeBaseIncl (TopCat.diskBoundary 4) z) =
    TopCat.diskBoundaryIncl 4 z
  rw [topologicalConeBaseIncl]
  change diskBoundaryFourConeHomeomorphDisk
      (topologicalConeCylinderIncl (TopCat.diskBoundary 4) (z, 0)) = _
  rw [diskBoundaryFourConeHomeomorphDisk_cylinder]
  apply ULift.ext
  apply Subtype.ext
  change (1 - (TopCat.I.homeomorph (0 : TopCat.I.{0}) : ℝ)) •
      z.down.val = z.down.val
  rw [TopCat.I.homeomorph_zero]
  norm_num

/-- Replace the cone summand in the Hopf mapping cone by the radially homeomorphic four-disk. -/
noncomputable def complexProjectivePlaneMappingConeToCell :
    topologicalMappingCone diskBoundaryFourComplexHopfMap ⟶
      cellAttachment diskBoundaryFourComplexHopfMap :=
  pushout.desc
    (cellAttachmentIncl diskBoundaryFourComplexHopfMap)
    (diskBoundaryFourConeIsoDisk.hom ≫
      cellAttachmentDisk diskBoundaryFourComplexHopfMap)
    (by
      rw [cellAttachment_condition, ← Category.assoc,
        diskBoundaryFourConeBaseIncl_isoDisk])

@[reassoc (attr := simp)]
theorem complexProjectivePlaneMappingConeIncl_toCell :
    topologicalMappingConeIncl diskBoundaryFourComplexHopfMap ≫
        complexProjectivePlaneMappingConeToCell =
      cellAttachmentIncl diskBoundaryFourComplexHopfMap :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem complexProjectivePlaneMappingConeConeIncl_toCell :
    topologicalMappingConeConeIncl diskBoundaryFourComplexHopfMap ≫
        complexProjectivePlaneMappingConeToCell =
      diskBoundaryFourConeIsoDisk.hom ≫
        cellAttachmentDisk diskBoundaryFourComplexHopfMap :=
  pushout.inr_desc _ _ _

/-- Replace the disk summand in the Hopf cell attachment by the inverse cone model. -/
noncomputable def complexProjectivePlaneCellToMappingCone :
    cellAttachment diskBoundaryFourComplexHopfMap ⟶
      topologicalMappingCone diskBoundaryFourComplexHopfMap :=
  cellAttachmentDesc diskBoundaryFourComplexHopfMap
    (topologicalMappingConeIncl diskBoundaryFourComplexHopfMap)
    (diskBoundaryFourConeIsoDisk.inv ≫
      topologicalMappingConeConeIncl diskBoundaryFourComplexHopfMap)
    (by
      rw [topologicalMappingCone_condition, ← Category.assoc,
        ← diskBoundaryFourConeBaseIncl_isoDisk]
      simp)

@[reassoc (attr := simp)]
theorem complexProjectivePlaneCellIncl_toMappingCone :
    cellAttachmentIncl diskBoundaryFourComplexHopfMap ≫
        complexProjectivePlaneCellToMappingCone =
      topologicalMappingConeIncl diskBoundaryFourComplexHopfMap :=
  cellAttachmentIncl_desc _ _ _ _

@[reassoc (attr := simp)]
theorem complexProjectivePlaneCellDisk_toMappingCone :
    cellAttachmentDisk diskBoundaryFourComplexHopfMap ≫
        complexProjectivePlaneCellToMappingCone =
      diskBoundaryFourConeIsoDisk.inv ≫
        topologicalMappingConeConeIncl diskBoundaryFourComplexHopfMap :=
  cellAttachmentDisk_desc _ _ _ _

theorem complexProjectivePlaneMappingConeToCell_comp_toMappingCone :
    complexProjectivePlaneMappingConeToCell ≫
        complexProjectivePlaneCellToMappingCone =
      𝟙 (topologicalMappingCone diskBoundaryFourComplexHopfMap) := by
  apply topologicalMappingCone_hom_ext diskBoundaryFourComplexHopfMap
  · simp
  · simp

theorem complexProjectivePlaneCellToMappingCone_comp_toCell :
    complexProjectivePlaneCellToMappingCone ≫
        complexProjectivePlaneMappingConeToCell =
      𝟙 (cellAttachment diskBoundaryFourComplexHopfMap) := by
  apply cellAttachment_hom_ext diskBoundaryFourComplexHopfMap
  · simp
  · simp

/-- The mapping cone of the exact Hopf attaching map is isomorphic to its four-cell
attachment. -/
noncomputable def complexProjectivePlaneMappingConeIsoCell :
    topologicalMappingCone diskBoundaryFourComplexHopfMap ≅
      cellAttachment diskBoundaryFourComplexHopfMap where
  hom := complexProjectivePlaneMappingConeToCell
  inv := complexProjectivePlaneCellToMappingCone
  hom_inv_id := complexProjectivePlaneMappingConeToCell_comp_toMappingCone
  inv_hom_id := complexProjectivePlaneCellToMappingCone_comp_toCell

/-- The mapping cone of the exact Hopf attaching map is homeomorphic to the Hopf cell model. -/
noncomputable def complexProjectivePlaneMappingConeHomeomorphCell :
    topologicalMappingCone diskBoundaryFourComplexHopfMap ≃ₜ
      cellAttachment diskBoundaryFourComplexHopfMap :=
  TopCat.homeoOfIso complexProjectivePlaneMappingConeIsoCell

/-- The mapping cone of the exact Hopf attaching map is complex projective two-space. -/
noncomputable def complexProjectivePlaneMappingConeHomeomorph :
    topologicalMappingCone diskBoundaryFourComplexHopfMap ≃ₜ
      ComplexProjectiveModel 2 :=
  complexProjectivePlaneMappingConeHomeomorphCell.trans
    complexProjectivePlaneCellHomeomorph

@[simp]
theorem complexProjectivePlaneMappingConeHomeomorph_incl
    (p : ComplexProjectiveModel 1) :
    complexProjectivePlaneMappingConeHomeomorph
        (topologicalMappingConeIncl diskBoundaryFourComplexHopfMap p) =
      complexProjectivePlaneBottomIncl p := by
  change complexProjectivePlaneCellHomeomorph
      (complexProjectivePlaneMappingConeToCell
        (topologicalMappingConeIncl diskBoundaryFourComplexHopfMap p)) = _
  rw [show complexProjectivePlaneMappingConeToCell
      (topologicalMappingConeIncl diskBoundaryFourComplexHopfMap p) =
      cellAttachmentIncl diskBoundaryFourComplexHopfMap p from
    ConcreteCategory.congr_hom complexProjectivePlaneMappingConeIncl_toCell p]
  exact complexProjectivePlaneCellHomeomorph_incl p

@[simp]
theorem complexProjectivePlaneMappingConeHomeomorph_cylinder
    (c : TopCat.diskBoundary.{0} 4 × TopCat.I.{0}) :
    complexProjectivePlaneMappingConeHomeomorph
        (topologicalMappingConeConeIncl diskBoundaryFourComplexHopfMap
          (topologicalConeCylinderIncl (TopCat.diskBoundary 4) c)) =
      complexProjectivePlaneCharacteristic
        (diskBoundaryFourConeCylinderToDisk c) := by
  change complexProjectivePlaneCellHomeomorph
      (complexProjectivePlaneMappingConeToCell
        (topologicalMappingConeConeIncl diskBoundaryFourComplexHopfMap
          (topologicalConeCylinderIncl (TopCat.diskBoundary 4) c))) = _
  rw [show complexProjectivePlaneMappingConeToCell
      (topologicalMappingConeConeIncl diskBoundaryFourComplexHopfMap
        (topologicalConeCylinderIncl (TopCat.diskBoundary 4) c)) =
      cellAttachmentDisk diskBoundaryFourComplexHopfMap
        (diskBoundaryFourConeCylinderToDisk c) by
    rw [show complexProjectivePlaneMappingConeToCell
        (topologicalMappingConeConeIncl diskBoundaryFourComplexHopfMap
          (topologicalConeCylinderIncl (TopCat.diskBoundary 4) c)) =
        (diskBoundaryFourConeIsoDisk.hom ≫
          cellAttachmentDisk diskBoundaryFourComplexHopfMap)
            (topologicalConeCylinderIncl (TopCat.diskBoundary 4) c) from
      ConcreteCategory.congr_hom
        complexProjectivePlaneMappingConeConeIncl_toCell
        (topologicalConeCylinderIncl (TopCat.diskBoundary 4) c)]
    change cellAttachmentDisk diskBoundaryFourComplexHopfMap
      (diskBoundaryFourConeHomeomorphDisk
        (topologicalConeCylinderIncl (TopCat.diskBoundary 4) c)) = _
    rw [diskBoundaryFourConeHomeomorphDisk_cylinder]]
  exact complexProjectivePlaneCellHomeomorph_disk _

/-! ## The cofiber collapse -/

theorem diskBoundaryFourIncl_diskToSphere :
    TopCat.diskBoundaryIncl 4 ≫ TopCat.ofHom (diskToSphere 4) =
      TopCat.const (sphereBasepoint 4) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact diskToSphere_boundary 4 _
    (mem_sphere_zero_iff_norm.mp z.down.property)

/-- Identify the suspension of the four-disk boundary with the quotient four-sphere. -/
noncomputable def diskBoundaryFourSuspensionToSphere :
    topologicalSuspension (TopCat.diskBoundary.{0} 4) ⟶
      TopCat.of (Sph 4) :=
  pushout.desc
    (TopCat.const (sphereBasepoint 4))
    (diskBoundaryFourConeIsoDisk.hom ≫ TopCat.ofHom (diskToSphere 4))
    (by
      rw [← Category.assoc, diskBoundaryFourConeBaseIncl_isoDisk,
        diskBoundaryFourIncl_diskToSphere]
      rfl)

@[reassoc (attr := simp)]
theorem diskBoundaryFourSuspensionPointIncl_toSphere :
    topologicalSuspensionPointIncl (TopCat.diskBoundary.{0} 4) ≫
        diskBoundaryFourSuspensionToSphere =
      TopCat.const (sphereBasepoint 4) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem diskBoundaryFourSuspensionConeIncl_toSphere :
    topologicalSuspensionConeIncl (TopCat.diskBoundary.{0} 4) ≫
        diskBoundaryFourSuspensionToSphere =
      diskBoundaryFourConeIsoDisk.hom ≫ TopCat.ofHom (diskToSphere 4) :=
  pushout.inr_desc _ _ _

/-- Under the cone-to-disk comparison, the abstract mapping-cone collapse is exactly the
previously constructed collapse of the Hopf cell model to the four-sphere. -/
theorem complexProjectivePlaneMappingCone_collapse_square :
    complexProjectivePlaneMappingConeToCell ≫
        complexProjectivePlaneCellCollapse =
      topologicalMappingConeCollapse diskBoundaryFourComplexHopfMap ≫
        diskBoundaryFourSuspensionToSphere := by
  apply topologicalMappingCone_hom_ext diskBoundaryFourComplexHopfMap
  · simp
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    rfl
  · simp
    rfl

/-! ## The suspension of the disk boundary is the quotient sphere -/

theorem diskToSphereFour_eq_iff
    (x y : TopCat.disk.{0} 4) :
    diskToSphere 4 x = diskToSphere 4 y ↔
      x = y ∨ (‖x.down.val‖ = 1 ∧ ‖y.down.val‖ = 1) := by
  rw [diskToSphere]
  constructor
  · intro h
    rcases (closedDiskToSphere_eq_iff 4 x.down y.down).mp h with hxy | hbd
    · left
      apply ULift.ext
      exact hxy
    · exact Or.inr hbd
  · rintro (rfl | hbd)
    · rfl
    · exact (closedDiskToSphere_eq_iff 4 x.down y.down).mpr (Or.inr hbd)

theorem diskToSphereFour_eq_basepoint_iff
    (x : TopCat.disk.{0} 4) :
    diskToSphere 4 x = sphereBasepoint 4 ↔ ‖x.down.val‖ = 1 := by
  let z : TopCat.diskBoundary.{0} 4 :=
    ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩
  have hz : ‖(TopCat.diskBoundaryIncl 4 z).down.val‖ = 1 := by
    change ‖EuclideanSpace.single 0 1‖ = 1
    simp
  have hbase : diskToSphere 4 (TopCat.diskBoundaryIncl 4 z) =
      sphereBasepoint 4 := diskToSphere_boundary 4 _ hz
  constructor
  · intro hx
    have hEq : diskToSphere 4 x =
        diskToSphere 4 (TopCat.diskBoundaryIncl 4 z) := hx.trans hbase.symm
    rcases (diskToSphereFour_eq_iff x
      (TopCat.diskBoundaryIncl 4 z)).mp hEq with h | h
    · rw [h]
      exact hz
    · exact h.1
  · intro hx
    exact diskToSphere_boundary 4 x hx

/-- The quotient map from a four-cell attached to a point onto the four-sphere. -/
noncomputable def diskBoundaryFourCellSphereMap :
    cellAttachment (toUnit (TopCat.diskBoundary.{0} 4)) ⟶
      TopCat.of (Sph 4) :=
  cellAttachmentDesc (toUnit (TopCat.diskBoundary 4))
    (TopCat.const (sphereBasepoint 4))
    (TopCat.ofHom (diskToSphere 4)) (by
      rw [diskBoundaryFourIncl_diskToSphere]
      rfl)

@[reassoc (attr := simp)]
theorem diskBoundaryFourCellSphereMap_incl :
    cellAttachmentIncl (toUnit (TopCat.diskBoundary.{0} 4)) ≫
        diskBoundaryFourCellSphereMap =
      TopCat.const (sphereBasepoint 4) :=
  cellAttachmentIncl_desc _ _ _ _

@[reassoc (attr := simp)]
theorem diskBoundaryFourCellSphereMap_disk :
    cellAttachmentDisk (toUnit (TopCat.diskBoundary.{0} 4)) ≫
        diskBoundaryFourCellSphereMap =
      TopCat.ofHom (diskToSphere 4) :=
  cellAttachmentDisk_desc _ _ _ _

@[simp]
theorem diskBoundaryFourCellSphereMap_incl_apply (u : PUnit) :
    diskBoundaryFourCellSphereMap
        (cellAttachmentIncl (toUnit (TopCat.diskBoundary 4)) u) =
      sphereBasepoint 4 :=
  ConcreteCategory.congr_hom diskBoundaryFourCellSphereMap_incl u

@[simp]
theorem diskBoundaryFourCellSphereMap_disk_apply
    (x : TopCat.disk.{0} 4) :
    diskBoundaryFourCellSphereMap
        (cellAttachmentDisk (toUnit (TopCat.diskBoundary 4)) x) =
      diskToSphere 4 x :=
  ConcreteCategory.congr_hom diskBoundaryFourCellSphereMap_disk x

@[simp]
theorem diskBoundaryFourCellSumDesc_inl (u : PUnit) :
    pushoutSumDesc (toUnit (TopCat.diskBoundary 4))
        (TopCat.diskBoundaryIncl 4) (Sum.inl u) =
      cellAttachmentIncl (toUnit (TopCat.diskBoundary 4)) u :=
  rfl

@[simp]
theorem diskBoundaryFourCellSumDesc_inr (x : TopCat.disk.{0} 4) :
    pushoutSumDesc (toUnit (TopCat.diskBoundary 4))
        (TopCat.diskBoundaryIncl 4) (Sum.inr x) =
      cellAttachmentDisk (toUnit (TopCat.diskBoundary 4)) x :=
  rfl

theorem diskBoundaryFourCellSphereMap_surjective :
    Function.Surjective diskBoundaryFourCellSphereMap := by
  intro y
  obtain ⟨x, rfl⟩ := diskToSphere_surjective 3 y
  exact ⟨cellAttachmentDisk (toUnit (TopCat.diskBoundary 4)) x,
    ConcreteCategory.congr_hom diskBoundaryFourCellSphereMap_disk x⟩

theorem diskBoundaryFourCellDisk_eq_incl_of_norm_eq_one
    (x : TopCat.disk.{0} 4) (hx : ‖x.down.val‖ = 1) :
    cellAttachmentDisk (toUnit (TopCat.diskBoundary 4)) x =
      cellAttachmentIncl (toUnit (TopCat.diskBoundary 4)) PUnit.unit := by
  let z : TopCat.diskBoundary.{0} 4 :=
    ULift.up ⟨x.down.val, mem_sphere_zero_iff_norm.mpr hx⟩
  have hz : TopCat.diskBoundaryIncl 4 z = x := by
    apply ULift.ext
    apply Subtype.ext
    rfl
  have hc := ConcreteCategory.congr_hom
    (cellAttachment_condition (toUnit (TopCat.diskBoundary 4))) z
  change cellAttachmentIncl (toUnit (TopCat.diskBoundary 4)) PUnit.unit =
    cellAttachmentDisk (toUnit (TopCat.diskBoundary 4))
      (TopCat.diskBoundaryIncl 4 z) at hc
  rw [hz] at hc
  exact hc.symm

theorem diskBoundaryFourCellSphereMap_injective :
    Function.Injective diskBoundaryFourCellSphereMap := by
  intro p q h
  obtain ⟨sp, rfl⟩ :=
    (pushoutSumDesc_isQuotientMap
      (toUnit (TopCat.diskBoundary 4)) (TopCat.diskBoundaryIncl 4)).surjective p
  obtain ⟨sq, rfl⟩ :=
    (pushoutSumDesc_isQuotientMap
      (toUnit (TopCat.diskBoundary 4)) (TopCat.diskBoundaryIncl 4)).surjective q
  rcases sp with u | x <;> rcases sq with v | y
  · change PUnit at u v
    cases u
    cases v
    rfl
  · have hy : diskToSphere 4 y = sphereBasepoint 4 := by
      have hcell : diskBoundaryFourCellSphereMap
          (cellAttachmentIncl (toUnit (TopCat.diskBoundary 4)) u) =
        diskBoundaryFourCellSphereMap
          (cellAttachmentDisk (toUnit (TopCat.diskBoundary 4)) y) := by
        simpa only [diskBoundaryFourCellSumDesc_inl,
          diskBoundaryFourCellSumDesc_inr] using h
      exact (diskBoundaryFourCellSphereMap_disk_apply y).symm.trans
        (hcell.symm.trans (diskBoundaryFourCellSphereMap_incl_apply u))
    have hynorm := (diskToSphereFour_eq_basepoint_iff y).mp hy
    change PUnit at u
    cases u
    exact (diskBoundaryFourCellDisk_eq_incl_of_norm_eq_one y hynorm).symm
  · have hx : diskToSphere 4 x = sphereBasepoint 4 := by
      have hcell : diskBoundaryFourCellSphereMap
          (cellAttachmentDisk (toUnit (TopCat.diskBoundary 4)) x) =
        diskBoundaryFourCellSphereMap
          (cellAttachmentIncl (toUnit (TopCat.diskBoundary 4)) v) := by
        simpa only [diskBoundaryFourCellSumDesc_inl,
          diskBoundaryFourCellSumDesc_inr] using h
      exact (diskBoundaryFourCellSphereMap_disk_apply x).symm.trans
        (hcell.trans (diskBoundaryFourCellSphereMap_incl_apply v))
    have hxnorm := (diskToSphereFour_eq_basepoint_iff x).mp hx
    change PUnit at v
    cases v
    exact diskBoundaryFourCellDisk_eq_incl_of_norm_eq_one x hxnorm
  · have hxy : diskToSphere 4 x = diskToSphere 4 y := by
      have hcell : diskBoundaryFourCellSphereMap
          (cellAttachmentDisk (toUnit (TopCat.diskBoundary 4)) x) =
        diskBoundaryFourCellSphereMap
          (cellAttachmentDisk (toUnit (TopCat.diskBoundary 4)) y) := by
        simpa only [diskBoundaryFourCellSumDesc_inr] using h
      exact (diskBoundaryFourCellSphereMap_disk_apply x).symm.trans
        (hcell.trans (diskBoundaryFourCellSphereMap_disk_apply y))
    rcases (diskToSphereFour_eq_iff x y).mp hxy with hxy | ⟨hx, hy⟩
    · subst y
      rfl
    · exact (diskBoundaryFourCellDisk_eq_incl_of_norm_eq_one x hx).trans
        (diskBoundaryFourCellDisk_eq_incl_of_norm_eq_one y hy).symm

noncomputable instance diskBoundaryFourCellCompactSpace :
    CompactSpace (cellAttachment (toUnit (TopCat.diskBoundary.{0} 4))) := by
  letI : CompactSpace ((𝟙_ TopCat.{0} : TopCat.{0}) : Type) := by
    change CompactSpace PUnit
    infer_instance
  exact cellAttachmentCompactSpace (toUnit (TopCat.diskBoundary 4))

/-- Attaching a four-disk to a point along its whole boundary gives the four-sphere. -/
noncomputable def diskBoundaryFourCellHomeomorphSphere :
    cellAttachment (toUnit (TopCat.diskBoundary.{0} 4)) ≃ₜ Sph 4 :=
  IsHomeomorph.homeomorph diskBoundaryFourCellSphereMap <|
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨diskBoundaryFourCellSphereMap.hom.continuous,
        diskBoundaryFourCellSphereMap_injective,
        diskBoundaryFourCellSphereMap_surjective⟩

/-- Replace a cone on `∂D⁴` by the radially homeomorphic disk in any mapping cone. -/
noncomputable def diskBoundaryFourMappingConeToCell
    {X : TopCat.{0}} (a : TopCat.diskBoundary 4 ⟶ X) :
    topologicalMappingCone a ⟶ cellAttachment a :=
  pushout.desc (cellAttachmentIncl a)
    (diskBoundaryFourConeIsoDisk.hom ≫ cellAttachmentDisk a) (by
      rw [cellAttachment_condition, ← Category.assoc,
        diskBoundaryFourConeBaseIncl_isoDisk])

noncomputable def diskBoundaryFourCellToMappingCone
    {X : TopCat.{0}} (a : TopCat.diskBoundary 4 ⟶ X) :
    cellAttachment a ⟶ topologicalMappingCone a :=
  cellAttachmentDesc a (topologicalMappingConeIncl a)
    (diskBoundaryFourConeIsoDisk.inv ≫ topologicalMappingConeConeIncl a) (by
      rw [topologicalMappingCone_condition, ← Category.assoc,
        ← diskBoundaryFourConeBaseIncl_isoDisk]
      simp)

@[reassoc (attr := simp)]
theorem diskBoundaryFourMappingConeIncl_toCell
    {X : TopCat.{0}} (a : TopCat.diskBoundary 4 ⟶ X) :
    topologicalMappingConeIncl a ≫ diskBoundaryFourMappingConeToCell a =
      cellAttachmentIncl a :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem diskBoundaryFourMappingConeConeIncl_toCell
    {X : TopCat.{0}} (a : TopCat.diskBoundary 4 ⟶ X) :
    topologicalMappingConeConeIncl a ≫ diskBoundaryFourMappingConeToCell a =
      diskBoundaryFourConeIsoDisk.hom ≫ cellAttachmentDisk a :=
  pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
theorem diskBoundaryFourCellIncl_toMappingCone
    {X : TopCat.{0}} (a : TopCat.diskBoundary 4 ⟶ X) :
    cellAttachmentIncl a ≫ diskBoundaryFourCellToMappingCone a =
      topologicalMappingConeIncl a :=
  cellAttachmentIncl_desc _ _ _ _

@[reassoc (attr := simp)]
theorem diskBoundaryFourCellDisk_toMappingCone
    {X : TopCat.{0}} (a : TopCat.diskBoundary 4 ⟶ X) :
    cellAttachmentDisk a ≫ diskBoundaryFourCellToMappingCone a =
      diskBoundaryFourConeIsoDisk.inv ≫ topologicalMappingConeConeIncl a :=
  cellAttachmentDisk_desc _ _ _ _

noncomputable def diskBoundaryFourMappingConeIsoCell
    {X : TopCat.{0}} (a : TopCat.diskBoundary 4 ⟶ X) :
    topologicalMappingCone a ≅ cellAttachment a where
  hom := diskBoundaryFourMappingConeToCell a
  inv := diskBoundaryFourCellToMappingCone a
  hom_inv_id := by
    apply topologicalMappingCone_hom_ext a
    · simp
    · simp
  inv_hom_id := by
    apply cellAttachment_hom_ext a
    · simp
    · simp

/-- The suspension of the boundary of the four-disk is the four-sphere. -/
noncomputable def diskBoundaryFourSuspensionHomeomorphSphere :
    topologicalSuspension (TopCat.diskBoundary.{0} 4) ≃ₜ Sph 4 :=
  (TopCat.homeoOfIso
    (diskBoundaryFourMappingConeIsoCell
      (toUnit (TopCat.diskBoundary 4)))).trans
    diskBoundaryFourCellHomeomorphSphere

theorem diskBoundaryFourSuspension_comparison :
    diskBoundaryFourMappingConeToCell
          (toUnit (TopCat.diskBoundary 4)) ≫
        diskBoundaryFourCellSphereMap =
      diskBoundaryFourSuspensionToSphere := by
  apply topologicalMappingCone_hom_ext (toUnit (TopCat.diskBoundary 4))
  · simp
    exact diskBoundaryFourSuspensionPointIncl_toSphere.symm
  · simp
    exact diskBoundaryFourSuspensionConeIncl_toSphere.symm

@[simp]
theorem diskBoundaryFourSuspensionHomeomorphSphere_apply
    (x : topologicalSuspension (TopCat.diskBoundary.{0} 4)) :
    diskBoundaryFourSuspensionHomeomorphSphere x =
      diskBoundaryFourSuspensionToSphere x := by
  change (diskBoundaryFourMappingConeToCell
      (toUnit (TopCat.diskBoundary 4)) ≫
        diskBoundaryFourCellSphereMap) x = _
  exact ConcreteCategory.congr_hom diskBoundaryFourSuspension_comparison x

/-! ## The canonical cofiber collapse has no homotopy section -/

noncomputable def complexProjectivePlaneMappingConeBasepoint :
    topologicalMappingCone diskBoundaryFourComplexHopfMap :=
  topologicalMappingConeIncl diskBoundaryFourComplexHopfMap
    (complexProjectiveModelBasepoint 1)

@[simp]
theorem complexProjectivePlaneMappingConeHomeomorphCell_basepoint :
    complexProjectivePlaneMappingConeHomeomorphCell
        complexProjectivePlaneMappingConeBasepoint =
      complexProjectivePlaneCellBasepoint := by
  change complexProjectivePlaneMappingConeToCell
      complexProjectivePlaneMappingConeBasepoint = _
  exact ConcreteCategory.congr_hom complexProjectivePlaneMappingConeIncl_toCell _

theorem piFour_complexProjectivePlaneMappingCone_subsingleton :
    Subsingleton
      (π_ 4 (topologicalMappingCone diskBoundaryFourComplexHopfMap)
        complexProjectivePlaneMappingConeBasepoint) := by
  let e := HomotopyGroup.homeomorphMulEquivOfEq (N := Fin 4)
    complexProjectivePlaneMappingConeHomeomorphCell
    complexProjectivePlaneMappingConeHomeomorphCell_basepoint
  exact e.toEquiv.subsingleton_congr.mpr
    piFour_complexProjectivePlaneCell_subsingleton

noncomputable def diskBoundaryFourSuspensionBasepoint :
    topologicalSuspension (TopCat.diskBoundary.{0} 4) :=
  topologicalSuspensionPointIncl (TopCat.diskBoundary 4) PUnit.unit

@[simp]
theorem diskBoundaryFourSuspensionHomeomorphSphere_basepoint :
    diskBoundaryFourSuspensionHomeomorphSphere
        diskBoundaryFourSuspensionBasepoint = sphereBasepoint 4 := by
  rw [diskBoundaryFourSuspensionHomeomorphSphere_apply]
  exact ConcreteCategory.congr_hom
    diskBoundaryFourSuspensionPointIncl_toSphere PUnit.unit

@[simp]
theorem complexProjectivePlaneMappingConeCollapse_basepoint :
    topologicalMappingConeCollapse diskBoundaryFourComplexHopfMap
        complexProjectivePlaneMappingConeBasepoint =
      diskBoundaryFourSuspensionBasepoint := by
  exact ConcreteCategory.congr_hom
    (topologicalMappingConeIncl_collapse diskBoundaryFourComplexHopfMap)
    (complexProjectiveModelBasepoint 1)

/-- The canonical cofiber collapse from the exact Hopf mapping cone to the suspension of its
attaching sphere has no based homotopy section. -/
theorem not_exists_complexProjectivePlaneMappingConeCollapse_homotopy_section :
    ¬ ∃ (s : C(topologicalSuspension (TopCat.diskBoundary.{0} 4),
        topologicalMappingCone diskBoundaryFourComplexHopfMap))
        (_hs : s diskBoundaryFourSuspensionBasepoint =
          complexProjectivePlaneMappingConeBasepoint),
      ((topologicalMappingConeCollapse diskBoundaryFourComplexHopfMap).hom.comp s).HomotopicRel
        (ContinuousMap.id (topologicalSuspension (TopCat.diskBoundary.{0} 4)))
        {diskBoundaryFourSuspensionBasepoint} := by
  rintro ⟨s, hs, H⟩
  letI : Subsingleton
      (π_ 4 (topologicalMappingCone diskBoundaryFourComplexHopfMap)
        complexProjectivePlaneMappingConeBasepoint) :=
    piFour_complexProjectivePlaneMappingCone_subsingleton
  have hsurj : Function.Surjective
      (HomotopyGroup.map (N := Fin 4)
        (topologicalMappingConeCollapse diskBoundaryFourComplexHopfMap).hom
        complexProjectivePlaneMappingConeCollapse_basepoint) :=
    homotopyGroup_map_surjective_of_based_homotopy_section
      (topologicalMappingConeCollapse diskBoundaryFourComplexHopfMap).hom s
      complexProjectivePlaneMappingConeCollapse_basepoint hs H
  letI : Subsingleton
      (π_ 4 (topologicalSuspension (TopCat.diskBoundary.{0} 4))
        diskBoundaryFourSuspensionBasepoint) := hsurj.subsingleton
  let e := HomotopyGroup.homeomorphMulEquivOfEq (N := Fin 4)
    diskBoundaryFourSuspensionHomeomorphSphere
    diskBoundaryFourSuspensionHomeomorphSphere_basepoint
  letI : Subsingleton (π_ 4 (Sph 4) (sphereBasepoint 4)) :=
    e.toEquiv.subsingleton_congr.mp inferInstance
  exact sphereGeneratorClass_ne_one 3 (Subsingleton.elim _ _)

end Submission
