/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.ScaledAlignedPairGeneralPosition
import Submission.Approximation.CapExcisionClamp

/-!
# Stable general position for the two open cells of a sphere

The enlarged lower and upper caps of `Sph (d+1)` have disjoint open cell cores.  We model
conical neighborhoods of those cores directly in the ambient Euclidean space.  The defining
strict inequalities are homogeneous in the radial direction and include a harmless radius-two
cutoff, so they are exactly suited to `ScaledAlignedPairGeneralPosition`.

For a nowhere-zero locally Lipschitz ambient map, the stable dimension inequality therefore
selects a lower-cell direction `x` and an upper-cell direction `y` such that `x` is absent from
the image of the vertical prism over the projected `y`-fiber.  This is the geometric point
choice in the one-cell-per-side proof of homotopy excision.

## Main results

* `Submission.sphLowerCellAmbient`
* `Submission.sphUpperCellAmbient`
* `Submission.radialSphereCubeMap`
* `Submission.exists_sphereCell_pair_not_mem_prism_image`
* `Submission.exists_sphereCell_pair_not_mem_prism_image_of_stableRange`
-/

open Set
open scoped unitInterval Topology

noncomputable section

namespace Submission

variable {d n q : ℕ}

/-- The last ambient coordinate in the Euclidean model of `Sph (d+1)`. -/
def sphAmbientHeight (v : EuclideanSpace ℝ (Fin (d + 2))) : ℝ :=
  v (Fin.last (d + 1))

theorem continuous_sphAmbientHeight :
    Continuous (sphAmbientHeight (d := d)) :=
  PiLp.continuous_apply 2 (fun _ : Fin (d + 2) => ℝ) (Fin.last (d + 1))

/-- A truncated open cone whose radial directions lie strictly in the lower cap but outside the
upper cap. -/
def sphLowerCellAmbient (d : ℕ) : Set (EuclideanSpace ℝ (Fin (d + 2))) :=
  {v | ‖v‖ < 2 ∧ 3 * sphAmbientHeight v < -‖v‖}

/-- A truncated open cone whose radial directions lie strictly in the upper cap but outside the
lower cap. -/
def sphUpperCellAmbient (d : ℕ) : Set (EuclideanSpace ℝ (Fin (d + 2))) :=
  {v | ‖v‖ < 2 ∧ ‖v‖ < 3 * sphAmbientHeight v}

theorem isOpen_sphLowerCellAmbient : IsOpen (sphLowerCellAmbient d) := by
  exact (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt (continuous_const.mul continuous_sphAmbientHeight)
      continuous_norm.neg)

theorem isOpen_sphUpperCellAmbient : IsOpen (sphUpperCellAmbient d) := by
  exact (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_norm
      (continuous_const.mul continuous_sphAmbientHeight))

/-- The south pole, as a point of `Sph (d+1)`. -/
noncomputable def sphSouthPole (d : ℕ) : Sph (d + 1) :=
  sphPole d (-1) (by norm_num)

@[simp] theorem sphHeight_sphSouthPole (d : ℕ) :
    sphHeight (sphSouthPole d) = -1 := by
  simp [sphSouthPole]

theorem coe_sphSouthPole_mem_sphLowerCellAmbient (d : ℕ) :
    ((sphSouthPole d : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) ∈
      sphLowerCellAmbient d := by
  constructor
  · rw [norm_coe_sph]
    norm_num
  · change 3 * sphHeight (sphSouthPole d) <
      -‖((sphSouthPole d : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2)))‖
    rw [sphHeight_sphSouthPole, norm_coe_sph]
    norm_num

theorem coe_sphNorthPole_mem_sphUpperCellAmbient (d : ℕ) :
    ((sphNorthPole d : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) ∈
      sphUpperCellAmbient d := by
  constructor
  · rw [norm_coe_sph]
    norm_num
  · change ‖((sphNorthPole d : Sph (d + 1)) :
        EuclideanSpace ℝ (Fin (d + 2)))‖ <
      3 * sphHeight (sphNorthPole d)
    rw [sphHeight_sphNorthPole, norm_coe_sph]
    norm_num

theorem sphLowerCellAmbient_nonempty : (sphLowerCellAmbient d).Nonempty :=
  ⟨_, coe_sphSouthPole_mem_sphLowerCellAmbient d⟩

theorem sphUpperCellAmbient_nonempty : (sphUpperCellAmbient d).Nonempty :=
  ⟨_, coe_sphNorthPole_mem_sphUpperCellAmbient d⟩

theorem norm_le_two_of_mem_sphLowerCellAmbient
    {v : EuclideanSpace ℝ (Fin (d + 2))} (hv : v ∈ sphLowerCellAmbient d) :
    ‖v‖ ≤ 2 :=
  hv.1.le

theorem norm_le_two_of_mem_sphUpperCellAmbient
    {v : EuclideanSpace ℝ (Fin (d + 2))} (hv : v ∈ sphUpperCellAmbient d) :
    ‖v‖ ≤ 2 :=
  hv.1.le

theorem ne_zero_of_mem_sphLowerCellAmbient
    {v : EuclideanSpace ℝ (Fin (d + 2))} (hv : v ∈ sphLowerCellAmbient d) :
    v ≠ 0 := by
  intro hzero
  subst v
  norm_num [sphLowerCellAmbient, sphAmbientHeight] at hv

theorem ne_zero_of_mem_sphUpperCellAmbient
    {v : EuclideanSpace ℝ (Fin (d + 2))} (hv : v ∈ sphUpperCellAmbient d) :
    v ≠ 0 := by
  intro hzero
  subst v
  norm_num [sphUpperCellAmbient, sphAmbientHeight] at hv

/-- Radial directions in the lower ambient cell have height strictly below `-1/3`. -/
theorem radialProj_height_lt_neg_third_of_mem_sphLowerCellAmbient
    {v : EuclideanSpace ℝ (Fin (d + 2))} (hv : v ∈ sphLowerCellAmbient d) :
    radialProj v (Fin.last (d + 1)) < -(1 / 3 : ℝ) := by
  have hv0 := ne_zero_of_mem_sphLowerCellAmbient hv
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  rw [radialProj, PiLp.smul_apply, smul_eq_mul, inv_mul_eq_div]
  apply (div_lt_iff₀ hvnorm).2
  change sphAmbientHeight v < -(1 / 3 : ℝ) * ‖v‖
  exact (by nlinarith [hv.2])

/-- Radial directions in the upper ambient cell have height strictly above `1/3`. -/
theorem third_lt_radialProj_height_of_mem_sphUpperCellAmbient
    {v : EuclideanSpace ℝ (Fin (d + 2))} (hv : v ∈ sphUpperCellAmbient d) :
    (1 / 3 : ℝ) < radialProj v (Fin.last (d + 1)) := by
  have hv0 := ne_zero_of_mem_sphUpperCellAmbient hv
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  rw [radialProj, PiLp.smul_apply, smul_eq_mul, inv_mul_eq_div]
  apply (lt_div_iff₀ hvnorm).2
  change (1 / 3 : ℝ) * ‖v‖ < sphAmbientHeight v
  exact (by nlinarith [hv.2])

/-- Bundle the radial projection of a nonzero ambient vector as a sphere point. -/
def radialSpherePoint
    (v : EuclideanSpace ℝ (Fin (d + 2))) (hv : v ≠ 0) : Sph (d + 1) :=
  ⟨radialProj v, mem_sphere_zero_iff_norm.mpr (norm_radialProj hv)⟩

@[simp] theorem coe_radialSpherePoint
    (v : EuclideanSpace ℝ (Fin (d + 2))) (hv : v ≠ 0) :
    ((radialSpherePoint v hv : Sph (d + 1)) :
      EuclideanSpace ℝ (Fin (d + 2))) = radialProj v :=
  rfl

/-- Bundle a nowhere-zero ambient cubical map as a sphere-valued map. -/
def radialSphereCubeMap
    (g : C(I^ Fin (n + 1), EuclideanSpace ℝ (Fin (d + 2))))
    (hne : ∀ y, g y ≠ 0) : C(I^ Fin (n + 1), Sph (d + 1)) where
  toFun y := radialSpherePoint (g y) (hne y)
  continuous_toFun := Continuous.subtype_mk
    (continuous_radialProj g.continuous hne) _

@[simp] theorem radialSphereCubeMap_apply
    (g : C(I^ Fin (n + 1), EuclideanSpace ℝ (Fin (d + 2))))
    (hne : ∀ y, g y ≠ 0) (y : I^ Fin (n + 1)) :
    radialSphereCubeMap g hne y = radialSpherePoint (g y) (hne y) :=
  rfl

theorem radialSpherePoint_not_mem_sphUpperCap_of_lowerCell
    {v : EuclideanSpace ℝ (Fin (d + 2))} (hv : v ∈ sphLowerCellAmbient d) :
    radialSpherePoint v (ne_zero_of_mem_sphLowerCellAmbient hv) ∉ sphUpperCap d := by
  rw [mem_sphUpperCap]
  change ¬ (-(1 / 3 : ℝ) ≤ radialProj v (Fin.last (d + 1)))
  exact not_le.mpr (radialProj_height_lt_neg_third_of_mem_sphLowerCellAmbient hv)

theorem radialSpherePoint_not_mem_sphLowerCap_of_upperCell
    {v : EuclideanSpace ℝ (Fin (d + 2))} (hv : v ∈ sphUpperCellAmbient d) :
    radialSpherePoint v (ne_zero_of_mem_sphUpperCellAmbient hv) ∉ sphLowerCap d := by
  rw [mem_sphLowerCap]
  change ¬ (radialProj v (Fin.last (d + 1)) ≤ (1 / 3 : ℝ))
  exact not_le.mpr (third_lt_radialProj_height_of_mem_sphUpperCellAmbient hv)

/-- The ambient radial prism-avoidance conclusion lifts to the sphere-valued map. -/
theorem not_mem_radialProjCubeMap_prism_imp_not_mem_radialSphereCubeMap_prism
    (g : C(I^ Fin (n + 1), EuclideanSpace ℝ (Fin (d + 2))))
    (hne : ∀ y, g y ≠ 0)
    {a b : EuclideanSpace ℝ (Fin (d + 2))} (ha : a ≠ 0) (hb : b ≠ 0)
    (havoid : radialProj a ∉
      radialProjCubeMap g hne ''
        cubeLastFiberPrism (radialProjCubeMap g hne) (radialProj b)) :
    radialSpherePoint a ha ∉
      radialSphereCubeMap g hne ''
        cubeLastFiberPrism (radialSphereCubeMap g hne) (radialSpherePoint b hb) := by
  rintro ⟨y, hyprism, hya⟩
  apply havoid
  refine ⟨y, ?_, congrArg Subtype.val hya⟩
  obtain ⟨t, hyt⟩ :=
    (mem_cubeLastFiberPrism_iff (radialSphereCubeMap g hne)
      (radialSpherePoint b hb) y).mp hyprism
  apply (mem_cubeLastFiberPrism_iff (radialProjCubeMap g hne) (radialProj b) y).mpr
  exact ⟨t, congrArg Subtype.val hyt⟩

/-- Stable general position supplies one point in each open spherical cell with the exact
vertical-prism avoidance relation consumed by `ProjectedFiberPrism`. -/
theorem exists_sphereCell_pair_not_mem_prism_image
    (g : C(I^ Fin (n + 1), EuclideanSpace ℝ (Fin (d + 2))))
    (hg : LocallyLipschitz g) (hne : ∀ y, g y ≠ 0)
    (hhalf : ∀ y, 1 / 2 ≤ ‖g y‖)
    (hdim : n + 4 < 2 * (d + 2)) :
    ∃ x y : Sph (d + 1),
      x ∉ sphUpperCap d ∧ y ∉ sphLowerCap d ∧
        x ∉ radialSphereCubeMap g hne ''
          cubeLastFiberPrism (radialSphereCubeMap g hne) y := by
  have hdim' : n + 4 <
      2 * Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 2))) := by
    rw [finrank_euclideanSpace_fin]
    exact hdim
  obtain ⟨a, ha, b, hb, hab⟩ := exists_radial_pair_not_mem_prism_image_in_open_sets
    g hg hne hhalf hdim'
    isOpen_sphLowerCellAmbient sphLowerCellAmbient_nonempty
    (fun _ h => norm_le_two_of_mem_sphLowerCellAmbient h)
    (fun _ h => ne_zero_of_mem_sphLowerCellAmbient h)
    isOpen_sphUpperCellAmbient sphUpperCellAmbient_nonempty
    (fun _ h => norm_le_two_of_mem_sphUpperCellAmbient h)
    (fun _ h => ne_zero_of_mem_sphUpperCellAmbient h)
  let ha0 := ne_zero_of_mem_sphLowerCellAmbient ha
  let hb0 := ne_zero_of_mem_sphUpperCellAmbient hb
  refine ⟨radialSpherePoint a ha0, radialSpherePoint b hb0,
    radialSpherePoint_not_mem_sphUpperCap_of_lowerCell ha,
    radialSpherePoint_not_mem_sphLowerCap_of_upperCell hb, ?_⟩
  exact not_mem_radialProjCubeMap_prism_imp_not_mem_radialSphereCubeMap_prism
    g hne ha0 hb0 hab

/-- Stable-range indexing for a `(q+3)`-cube, the dimension of the triad obstruction to
bijectivity in relative degree `q+2`. -/
theorem exists_sphereCell_pair_not_mem_prism_image_of_stableRange
    (g : C(I^ Fin (q + 3), EuclideanSpace ℝ (Fin (d + 2))))
    (hg : LocallyLipschitz g) (hne : ∀ y, g y ≠ 0)
    (hhalf : ∀ y, 1 / 2 ≤ ‖g y‖)
    (hrange : q + 3 ≤ 2 * d) :
    ∃ x y : Sph (d + 1),
      x ∉ sphUpperCap d ∧ y ∉ sphLowerCap d ∧
        x ∉ radialSphereCubeMap g hne ''
          cubeLastFiberPrism (radialSphereCubeMap g hne) y := by
  exact exists_sphereCell_pair_not_mem_prism_image
    (n := q + 2) g hg hne hhalf (by omega)

end Submission
