/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.MappingCone
import Submission.WhiteheadTheorem.Shapes.Disk

/-!
# Cones on positive-dimensional disk boundaries

Radial contraction identifies the abstract topological cone on the exact boundary of
`Dⁿ⁺¹` with the exact disk `Dⁿ⁺¹`. The comparison is explicit on the cone cylinder,
cone point, and base, and its base restriction is exactly the standard disk-boundary inclusion.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology TopCat

noncomputable section

namespace Submission

variable {n : ℕ}

/-- Send `(z, t)` in the cone cylinder on `∂Dⁿ⁺¹` to `(1 - t) z` in `Dⁿ⁺¹`. -/
noncomputable def diskBoundarySuccConeCylinderToDisk
    (p : TopCat.diskBoundary.{0} (n + 1) × TopCat.I.{0}) : TopCat.disk.{0} (n + 1) :=
  ULift.up ⟨(1 - (TopCat.I.homeomorph p.2 : ℝ)) • p.1.down.val, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg]
    · rw [mem_sphere_zero_iff_norm.mp p.1.down.property, mul_one]
      exact sub_le_self 1 (TopCat.I.homeomorph p.2).property.1
    · exact sub_nonneg.mpr (TopCat.I.homeomorph p.2).property.2⟩

theorem continuous_diskBoundarySuccConeCylinderToDisk :
    Continuous (diskBoundarySuccConeCylinderToDisk (n := n)) := by
  apply continuous_uliftUp.comp
  apply Continuous.subtype_mk
  fun_prop

noncomputable def diskBoundarySuccConeCylinderToDiskTopCat :
    TopCat.diskBoundary.{0} (n + 1) ⊗ TopCat.I.{0} ⟶ TopCat.disk.{0} (n + 1) :=
  TopCat.ofHom ⟨diskBoundarySuccConeCylinderToDisk,
    continuous_diskBoundarySuccConeCylinderToDisk⟩

noncomputable def diskSuccCenter : TopCat.disk.{0} (n + 1) :=
  ULift.up ⟨0, by simp⟩

/-- The radial cylinder map descends to the cone because its top is the disk center. -/
noncomputable def diskBoundarySuccConeToDisk :
    topologicalCone (TopCat.diskBoundary.{0} (n + 1)) ⟶ TopCat.disk.{0} (n + 1) :=
  topologicalConeDesc (TopCat.diskBoundary (n + 1))
    diskBoundarySuccConeCylinderToDiskTopCat
    (TopCat.const diskSuccCenter)
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
theorem diskBoundarySuccConeToDisk_cylinder
    (z : TopCat.diskBoundary.{0} (n + 1)) (t : TopCat.I.{0}) :
    diskBoundarySuccConeToDisk
        (topologicalConeCylinderIncl (TopCat.diskBoundary (n + 1)) (z, t)) =
      diskBoundarySuccConeCylinderToDisk (z, t) := by
  exact ConcreteCategory.congr_hom
    (topologicalConeCylinderIncl_desc (TopCat.diskBoundary (n + 1))
      diskBoundarySuccConeCylinderToDiskTopCat
      (TopCat.const diskSuccCenter) _) (z, t)

@[simp]
theorem diskBoundarySuccConeToDisk_point (u : PUnit) :
    diskBoundarySuccConeToDisk
        (topologicalConePointIncl (TopCat.diskBoundary (n + 1)) u) =
      diskSuccCenter := by
  exact ConcreteCategory.congr_hom
    (topologicalConePointIncl_desc (TopCat.diskBoundary (n + 1))
      diskBoundarySuccConeCylinderToDiskTopCat
      (TopCat.const diskSuccCenter) _) u

theorem diskBoundarySuccConeCylinderToDisk_surjective :
    Function.Surjective (diskBoundarySuccConeCylinderToDisk (n := n)) := by
  intro x
  by_cases hx : ‖x.down.val‖ = 0
  · let z : TopCat.diskBoundary.{0} (n + 1) :=
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
    let z : TopCat.diskBoundary.{0} (n + 1) := ULift.up
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

/-- The cone on a compact positive-dimensional disk boundary is compact. -/
noncomputable instance diskBoundarySuccConeCompactSpace :
    CompactSpace (topologicalCone (TopCat.diskBoundary.{0} (n + 1))) := by
  letI : CompactSpace TopCat.I.{0} :=
    TopCat.I.homeomorph.symm.compactSpace
  letI : CompactSpace
      ((TopCat.diskBoundary.{0} (n + 1) ⊗ TopCat.I.{0} : TopCat.{0}) : Type) := by
    change CompactSpace ((TopCat.diskBoundary.{0} (n + 1) : Type) × TopCat.I.{0})
    infer_instance
  letI : CompactSpace
      (((TopCat.diskBoundary.{0} (n + 1) ⊗ TopCat.I.{0} : TopCat.{0}) : Type) ⊕
        ((𝟙_ TopCat.{0} : TopCat.{0}) : Type)) := by
    change CompactSpace
      (((TopCat.diskBoundary.{0} (n + 1) : Type) × TopCat.I.{0}) ⊕ PUnit)
    infer_instance
  exact Function.Surjective.compactSpace
    (topologicalConeSumDesc_isQuotientMap
      (TopCat.diskBoundary (n + 1))).continuous
    (topologicalConeSumDesc_isQuotientMap
      (TopCat.diskBoundary (n + 1))).surjective

theorem diskBoundarySuccConeToDisk_surjective :
    Function.Surjective (diskBoundarySuccConeToDisk (n := n)) := by
  intro x
  obtain ⟨c, rfl⟩ := diskBoundarySuccConeCylinderToDisk_surjective x
  exact ⟨topologicalConeCylinderIncl (TopCat.diskBoundary (n + 1)) c,
    diskBoundarySuccConeToDisk_cylinder c.1 c.2⟩

theorem diskBoundarySuccConeCylinderIncl_eq_point_of_radial_eq_center
    (c : TopCat.diskBoundary.{0} (n + 1) × TopCat.I.{0})
    (h : diskBoundarySuccConeCylinderToDisk c = diskSuccCenter) :
    topologicalConeCylinderIncl (TopCat.diskBoundary (n + 1)) c =
      topologicalConePointIncl (TopCat.diskBoundary (n + 1)) PUnit.unit := by
  have hvec := congrArg (fun x : TopCat.disk.{0} (n + 1) ↦ x.down.val) h
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
      (TopCat.ι₁ : TopCat.diskBoundary.{0} (n + 1) ⟶
        TopCat.diskBoundary.{0} (n + 1) ⊗ TopCat.I.{0}) ≫
          topologicalConeCylinderIncl (TopCat.diskBoundary (n + 1)) =
        toUnit (TopCat.diskBoundary (n + 1)) ≫
          topologicalConePointIncl (TopCat.diskBoundary (n + 1)) :=
    pushout.condition
  have hc : c = (c.1, (1 : TopCat.I.{0})) := by
    apply Prod.ext
    · rfl
    · exact ht
  rw [hc]
  change (topologicalConeCylinderIncl (TopCat.diskBoundary (n + 1))).hom
      (c.1, (1 : TopCat.I.{0})) =
    (topologicalConePointIncl (TopCat.diskBoundary (n + 1))).hom PUnit.unit
  convert ConcreteCategory.congr_hom htop c.1 using 1 <;> rfl

theorem diskBoundarySuccConeCylinderToDisk_eq_imp_of_ne_center
    (c d : TopCat.diskBoundary.{0} (n + 1) × TopCat.I.{0})
    (h : diskBoundarySuccConeCylinderToDisk c =
      diskBoundarySuccConeCylinderToDisk d)
    (hc : diskBoundarySuccConeCylinderToDisk c ≠ diskSuccCenter) :
    c = d := by
  have hvec := congrArg (fun x : TopCat.disk.{0} (n + 1) ↦ x.down.val) h
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
theorem topologicalConeSumDesc_diskBoundarySucc_inl
    (c : TopCat.diskBoundary.{0} (n + 1) × TopCat.I.{0}) :
    topologicalConeSumDesc (TopCat.diskBoundary (n + 1)) (Sum.inl c) =
      topologicalConeCylinderIncl (TopCat.diskBoundary (n + 1)) c :=
  rfl

@[simp]
theorem topologicalConeSumDesc_diskBoundarySucc_inr
    (u : (𝟙_ TopCat.{0} : TopCat.{0})) :
    topologicalConeSumDesc (TopCat.diskBoundary (n + 1)) (Sum.inr u) =
      topologicalConePointIncl (TopCat.diskBoundary (n + 1)) u :=
  rfl

@[simp]
theorem diskBoundarySuccConeToDisk_cylinder_pair
    (c : TopCat.diskBoundary.{0} (n + 1) × TopCat.I.{0}) :
    diskBoundarySuccConeToDisk
        (topologicalConeCylinderIncl (TopCat.diskBoundary (n + 1)) c) =
      diskBoundarySuccConeCylinderToDisk c := by
  rcases c with ⟨z, t⟩
  exact diskBoundarySuccConeToDisk_cylinder z t

theorem diskBoundarySuccConeToDisk_injective :
    Function.Injective (diskBoundarySuccConeToDisk (n := n)) := by
  intro x y h
  obtain ⟨sx, rfl⟩ :=
    (topologicalConeSumDesc_isQuotientMap
      (TopCat.diskBoundary (n + 1))).surjective x
  obtain ⟨sy, rfl⟩ :=
    (topologicalConeSumDesc_isQuotientMap
      (TopCat.diskBoundary (n + 1))).surjective y
  rcases sx with c | u <;> rcases sy with d | v
  · have hrad : diskBoundarySuccConeCylinderToDisk c =
        diskBoundarySuccConeCylinderToDisk d := by
      simpa only [topologicalConeSumDesc_diskBoundarySucc_inl,
        diskBoundarySuccConeToDisk_cylinder_pair] using h
    by_cases hc : diskBoundarySuccConeCylinderToDisk c = diskSuccCenter
    · have hd : diskBoundarySuccConeCylinderToDisk d = diskSuccCenter :=
        hrad.symm.trans hc
      exact
        (diskBoundarySuccConeCylinderIncl_eq_point_of_radial_eq_center c hc).trans
          (diskBoundarySuccConeCylinderIncl_eq_point_of_radial_eq_center d hd).symm
    · have hcd :=
        diskBoundarySuccConeCylinderToDisk_eq_imp_of_ne_center c d hrad hc
      subst d
      rfl
  · have hrad : diskBoundarySuccConeCylinderToDisk c =
        diskSuccCenter := by
      simpa only [topologicalConeSumDesc_diskBoundarySucc_inl,
        topologicalConeSumDesc_diskBoundarySucc_inr,
        diskBoundarySuccConeToDisk_cylinder_pair,
        diskBoundarySuccConeToDisk_point] using h
    change PUnit at v
    cases v
    exact diskBoundarySuccConeCylinderIncl_eq_point_of_radial_eq_center c hrad
  · have hrad : diskSuccCenter =
        diskBoundarySuccConeCylinderToDisk d := by
      simpa only [topologicalConeSumDesc_diskBoundarySucc_inl,
        topologicalConeSumDesc_diskBoundarySucc_inr,
        diskBoundarySuccConeToDisk_cylinder_pair,
        diskBoundarySuccConeToDisk_point] using h
    change PUnit at u
    cases u
    exact (diskBoundarySuccConeCylinderIncl_eq_point_of_radial_eq_center d hrad.symm).symm
  · change PUnit at u v
    cases u
    cases v
    rfl

/-- The cone on `∂Dⁿ⁺¹` is radially homeomorphic to `Dⁿ⁺¹`. -/
noncomputable def diskBoundarySuccConeHomeomorphDisk :
    topologicalCone (TopCat.diskBoundary.{0} (n + 1)) ≃ₜ TopCat.disk.{0} (n + 1) := by
  letI : T2Space (TopCat.disk.{0} (n + 1)) := by
    unfold TopCat.disk
    infer_instance
  exact IsHomeomorph.homeomorph diskBoundarySuccConeToDisk <|
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨diskBoundarySuccConeToDisk.hom.continuous,
        diskBoundarySuccConeToDisk_injective,
        diskBoundarySuccConeToDisk_surjective⟩

@[simp]
theorem diskBoundarySuccConeHomeomorphDisk_cylinder
    (c : TopCat.diskBoundary.{0} (n + 1) × TopCat.I.{0}) :
    diskBoundarySuccConeHomeomorphDisk
        (topologicalConeCylinderIncl (TopCat.diskBoundary (n + 1)) c) =
      diskBoundarySuccConeCylinderToDisk c := by
  change diskBoundarySuccConeToDisk
      (topologicalConeCylinderIncl (TopCat.diskBoundary (n + 1)) c) = _
  exact diskBoundarySuccConeToDisk_cylinder_pair c

@[simp]
theorem diskBoundarySuccConeHomeomorphDisk_point (u : PUnit) :
    diskBoundarySuccConeHomeomorphDisk
        (topologicalConePointIncl (TopCat.diskBoundary (n + 1)) u) =
      diskSuccCenter := by
  change diskBoundarySuccConeToDisk
      (topologicalConePointIncl (TopCat.diskBoundary (n + 1)) u) = _
  exact diskBoundarySuccConeToDisk_point u

noncomputable def diskBoundarySuccConeIsoDisk :
    topologicalCone (TopCat.diskBoundary.{0} (n + 1)) ≅
      TopCat.disk.{0} (n + 1) :=
  TopCat.isoOfHomeo diskBoundarySuccConeHomeomorphDisk

@[reassoc]
theorem diskBoundarySuccConeBaseIncl_isoDisk :
    topologicalConeBaseIncl (TopCat.diskBoundary.{0} (n + 1)) ≫
        (diskBoundarySuccConeIsoDisk (n := n)).hom =
      TopCat.diskBoundaryIncl (n + 1) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change diskBoundarySuccConeHomeomorphDisk
      (topologicalConeBaseIncl (TopCat.diskBoundary (n + 1)) z) =
    TopCat.diskBoundaryIncl (n + 1) z
  rw [topologicalConeBaseIncl]
  change diskBoundarySuccConeHomeomorphDisk
      (topologicalConeCylinderIncl (TopCat.diskBoundary (n + 1)) (z, 0)) = _
  rw [diskBoundarySuccConeHomeomorphDisk_cylinder]
  apply ULift.ext
  apply Subtype.ext
  change (1 - (TopCat.I.homeomorph (0 : TopCat.I.{0}) : ℝ)) •
      z.down.val = z.down.val
  rw [TopCat.I.homeomorph_zero]
  norm_num

end Submission

