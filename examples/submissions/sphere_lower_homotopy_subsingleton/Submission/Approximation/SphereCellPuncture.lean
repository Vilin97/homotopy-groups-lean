/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.EndpointCapSqueezeSource

/-!
# Explicit puncture maps for the two open cells of a sphere

For an upper-cell point `y`, subtract the `y`-direction just far enough to replace the last
coordinate `h` by `min h 0`, then radially normalize.  The raw vector vanishes only at `y`.
The resulting punctured-sphere map lands in the lower cap, fixes the southern half-sphere, and
cannot newly hit a lower-cell point.

Dually, for a lower-cell point `x`, subtract a controlled multiple of `x` to raise negative
height towards zero.  At control value one this lands in the northern half-sphere; throughout
the deformation it preserves the lower cap.  Its raw vector can vanish only at `(1, x)`.

These formulas supply the explicit radial deformations used after stable two-cell compression.

## Main results

* `Submission.upperCellPunctureLower`
* `Submission.upperCellPunctureLower_mem_lowerCap`
* `Submission.upperCellPunctureLower_ne_of_ne`
* `Submission.lowerCellPunctureRaisePoint`
* `Submission.lowerCellPunctureRaisePoint_mem_lowerCap`
* `Submission.lowerCellPunctureRaisePoint_mem_upperCap_one`
-/

open Set
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {d : ℕ}

/-! ### Lowering away from a point in the upper open cell -/

/-- Coefficient of the chosen upper-cell direction that removes positive height. -/
def upperCellPunctureLowerCoeff (y z : Sph (d + 1)) : ℝ :=
  max (sphHeight z) 0 / sphHeight y

/-- The ambient vector underlying the upper-puncture lowering map. -/
def upperCellPunctureLowerAmbient (y z : Sph (d + 1)) :
    EuclideanSpace ℝ (Fin (d + 2)) :=
  z.1 - upperCellPunctureLowerCoeff y z • y.1

theorem continuous_upperCellPunctureLowerAmbient (y : Sph (d + 1)) :
    Continuous (upperCellPunctureLowerAmbient y) := by
  unfold upperCellPunctureLowerAmbient upperCellPunctureLowerCoeff
  exact continuous_subtype_val.sub
    (((continuous_sphHeight.max continuous_const).div_const _).smul
      continuous_const)

/-- The raw lowering formula replaces height by its nonpositive part. -/
theorem upperCellPunctureLowerAmbient_last
    (y z : Sph (d + 1)) (hy : sphHeight y ≠ 0) :
    upperCellPunctureLowerAmbient y z (Fin.last (d + 1)) =
      min (sphHeight z) 0 := by
  rw [upperCellPunctureLowerAmbient, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  change sphHeight z -
      (max (sphHeight z) 0 / sphHeight y) * sphHeight y =
    min (sphHeight z) 0
  rw [div_mul_cancel₀ _ hy]
  by_cases hz : 0 ≤ sphHeight z
  · rw [max_eq_left hz, min_eq_right hz]
    ring
  · have hz' : sphHeight z ≤ 0 := le_of_not_ge hz
    rw [max_eq_right hz', min_eq_left hz']
    ring

/-- With positive chosen height, the raw lowering vector can vanish only at the chosen point. -/
theorem upperCellPunctureLowerAmbient_eq_zero_imp
    (y z : Sph (d + 1)) (hy : 0 < sphHeight y)
    (hzero : upperCellPunctureLowerAmbient y z = 0) :
    z = y := by
  let a := upperCellPunctureLowerCoeff y z
  have heq : z.1 = a • y.1 := by
    exact sub_eq_zero.mp hzero
  have ha : 0 ≤ a := by
    exact div_nonneg (le_max_right _ _) hy.le
  have hnorm := congrArg norm heq
  have haone : a = 1 := by
    rw [norm_coe_sph, norm_smul, Real.norm_eq_abs,
      norm_coe_sph, abs_of_nonneg ha] at hnorm
    linarith
  apply Subtype.ext
  rw [heq, haone, one_smul]

theorem upperCellPunctureLowerAmbient_ne_zero
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    {z : Sph (d + 1)} (hz : z ≠ y) :
    upperCellPunctureLowerAmbient y z ≠ 0 :=
  fun hzero => hz (upperCellPunctureLowerAmbient_eq_zero_imp y z hy hzero)

/-! ### The controlled upper-puncture deformation -/

/-- Apply only a unit-interval fraction of the upper-puncture lowering formula. -/
def upperCellPunctureLowerAmbientAt
    (y : Sph (d + 1)) (u : I) (z : Sph (d + 1)) :
    EuclideanSpace ℝ (Fin (d + 2)) :=
  z.1 - ((u : ℝ) * upperCellPunctureLowerCoeff y z) • y.1

theorem continuous_upperCellPunctureLowerAmbientAt
    (y : Sph (d + 1)) :
    Continuous fun p : I × Sph (d + 1) =>
      upperCellPunctureLowerAmbientAt y p.1 p.2 := by
  unfold upperCellPunctureLowerAmbientAt upperCellPunctureLowerCoeff
  have hu : Continuous fun p : I × Sph (d + 1) => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : I × Sph (d + 1) => sphHeight p.2 :=
    continuous_sphHeight.comp continuous_snd
  exact (continuous_subtype_val.comp continuous_snd).sub
    ((hu.mul ((hz.max continuous_const).div_const _)).smul continuous_const)

/-- Controlled lowering changes height from `h` to `h - u * max h 0`. -/
theorem upperCellPunctureLowerAmbientAt_last
    (y : Sph (d + 1)) (hy : sphHeight y ≠ 0)
    (u : I) (z : Sph (d + 1)) :
    upperCellPunctureLowerAmbientAt y u z (Fin.last (d + 1)) =
      sphHeight z - (u : ℝ) * max (sphHeight z) 0 := by
  rw [upperCellPunctureLowerAmbientAt, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  change sphHeight z -
      ((u : ℝ) * (max (sphHeight z) 0 / sphHeight y)) * sphHeight y = _
  rw [mul_assoc, div_mul_cancel₀ _ hy]

/-- The controlled raw vector can vanish only at full strength at the chosen upper point. -/
theorem upperCellPunctureLowerAmbientAt_eq_zero_imp
    (y z : Sph (d + 1)) (hy : 0 < sphHeight y) (u : I)
    (hzero : upperCellPunctureLowerAmbientAt y u z = 0) :
    z = y ∧ u = 1 := by
  let a : ℝ := (u : ℝ) * upperCellPunctureLowerCoeff y z
  have heq : z.1 = a • y.1 := sub_eq_zero.mp hzero
  have ha : 0 ≤ a := by
    exact mul_nonneg u.2.1 (div_nonneg (le_max_right _ _) hy.le)
  have hnorm := congrArg norm heq
  have haone : a = 1 := by
    rw [norm_coe_sph, norm_smul, Real.norm_eq_abs,
      norm_coe_sph, abs_of_nonneg ha] at hnorm
    linarith
  have hzy : z = y := by
    apply Subtype.ext
    rw [heq, haone, one_smul]
  have haeq : a = (u : ℝ) := by
    dsimp only [a]
    rw [hzy, upperCellPunctureLowerCoeff, max_eq_left hy.le,
      div_self hy.ne', mul_one]
  have huval : (u : ℝ) = 1 := by linarith
  exact ⟨hzy, Subtype.ext huval⟩

theorem upperCellPunctureLowerAmbientAt_ne_zero
    (y z : Sph (d + 1)) (hy : 0 < sphHeight y) (u : I)
    (havoid : u = 1 → z ≠ y) :
    upperCellPunctureLowerAmbientAt y u z ≠ 0 := by
  intro hzero
  obtain ⟨hzy, hu⟩ :=
    upperCellPunctureLowerAmbientAt_eq_zero_imp y z hy u hzero
  exact havoid hu hzy

/-- Normalize controlled upper-puncture lowering to the sphere. -/
def upperCellPunctureLowerPointAt
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    (u : I) (z : Sph (d + 1)) (havoid : u = 1 → z ≠ y) :
    Sph (d + 1) :=
  radialSpherePoint (upperCellPunctureLowerAmbientAt y u z)
    (upperCellPunctureLowerAmbientAt_ne_zero y z hy u havoid)

@[simp] theorem upperCellPunctureLowerPointAt_zero
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    (z : Sph (d + 1)) (havoid : (0 : I) = 1 → z ≠ y) :
    upperCellPunctureLowerPointAt y hy 0 z havoid = z := by
  apply Subtype.ext
  change radialProj (upperCellPunctureLowerAmbientAt y 0 z) = z.1
  have hamb : upperCellPunctureLowerAmbientAt y 0 z = z.1 := by
    rw [upperCellPunctureLowerAmbientAt]
    norm_num
  rw [hamb, radialProj_of_norm_eq_one (norm_coe_sph z)]

/-- Controlled lowering preserves the closed northern half-sphere. -/
theorem upperCellPunctureLowerPointAt_height_nonneg
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    (u : I) {z : Sph (d + 1)} (hz : 0 ≤ sphHeight z)
    (havoid : u = 1 → z ≠ y) :
    0 ≤ sphHeight (upperCellPunctureLowerPointAt y hy u z havoid) := by
  change 0 ≤ radialProj (upperCellPunctureLowerAmbientAt y u z)
    (Fin.last (d + 1))
  apply radialProj_last_nonneg
  rw [upperCellPunctureLowerAmbientAt_last y hy.ne' u z,
    max_eq_left hz]
  have hmul := mul_nonneg (sub_nonneg.mpr u.2.2) hz
  nlinarith

/-- Nonpositive-height points are fixed throughout controlled lowering. -/
theorem upperCellPunctureLowerPointAt_eq_of_height_nonpos
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    (u : I) {z : Sph (d + 1)} (hz : sphHeight z ≤ 0)
    (havoid : u = 1 → z ≠ y) :
    upperCellPunctureLowerPointAt y hy u z havoid = z := by
  apply Subtype.ext
  change radialProj (upperCellPunctureLowerAmbientAt y u z) = z.1
  have hamb : upperCellPunctureLowerAmbientAt y u z = z.1 := by
    rw [upperCellPunctureLowerAmbientAt, upperCellPunctureLowerCoeff,
      max_eq_right hz, zero_div, mul_zero, zero_smul, sub_zero]
  rw [hamb, radialProj_of_norm_eq_one (norm_coe_sph z)]

/-- The sphere with one chosen point removed. -/
abbrev SphPointCompl (a : Sph (d + 1)) := {z : Sph (d + 1) // z ≠ a}

/-- Normalize the upper-puncture lowering formula to a sphere-valued map. -/
noncomputable def upperCellPunctureLower
    (y : Sph (d + 1)) (hy : 0 < sphHeight y) :
    C(SphPointCompl y, Sph (d + 1)) where
  toFun z := radialSpherePoint
    (upperCellPunctureLowerAmbient y z.1)
    (upperCellPunctureLowerAmbient_ne_zero y hy z.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_radialProj
    · exact (continuous_upperCellPunctureLowerAmbient y).comp
        continuous_subtype_val
    · intro z
      exact upperCellPunctureLowerAmbient_ne_zero y hy z.2

@[simp] theorem coe_upperCellPunctureLower
    (y : Sph (d + 1)) (hy : 0 < sphHeight y) (z : SphPointCompl y) :
    ((upperCellPunctureLower y hy z : Sph (d + 1)) :
      EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj (upperCellPunctureLowerAmbient y z.1) :=
  rfl

theorem upperCellPunctureLowerPointAt_one
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    (z : Sph (d + 1)) (hzy : z ≠ y) :
    upperCellPunctureLowerPointAt y hy 1 z (fun _ => hzy) =
      upperCellPunctureLower y hy ⟨z, hzy⟩ := by
  apply Subtype.ext
  change radialProj (upperCellPunctureLowerAmbientAt y 1 z) =
    radialProj (upperCellPunctureLowerAmbient y z)
  congr 1
  rw [upperCellPunctureLowerAmbientAt, upperCellPunctureLowerAmbient]
  norm_num

theorem sphHeight_upperCellPunctureLower_nonpos
    (y : Sph (d + 1)) (hy : 0 < sphHeight y) (z : SphPointCompl y) :
    sphHeight (upperCellPunctureLower y hy z) ≤ 0 := by
  change radialProj (upperCellPunctureLowerAmbient y z.1)
    (Fin.last (d + 1)) ≤ 0
  apply radialProj_last_nonpos
  rw [upperCellPunctureLowerAmbient_last y z.1 hy.ne']
  exact min_le_right _ _

theorem upperCellPunctureLower_mem_lowerCap
    (y : Sph (d + 1)) (hy : 0 < sphHeight y) (z : SphPointCompl y) :
    upperCellPunctureLower y hy z ∈ sphLowerCap d := by
  rw [mem_sphLowerCap]
  exact (sphHeight_upperCellPunctureLower_nonpos y hy z).trans (by norm_num)

/-- The lowering map fixes every nonpositive-height point. -/
theorem upperCellPunctureLower_eq_of_height_nonpos
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    {z : Sph (d + 1)} (hzy : z ≠ y) (hz : sphHeight z ≤ 0) :
    upperCellPunctureLower y hy ⟨z, hzy⟩ = z := by
  apply Subtype.ext
  change radialProj (upperCellPunctureLowerAmbient y z) = z.1
  have hamb : upperCellPunctureLowerAmbient y z = z.1 := by
    rw [upperCellPunctureLowerAmbient, upperCellPunctureLowerCoeff,
      max_eq_right hz, zero_div, zero_smul, sub_zero]
  rw [hamb, radialProj_of_norm_eq_one (norm_coe_sph z)]

/-- Lowering away from `y` cannot create a hit of a negative-height point `x`. -/
theorem upperCellPunctureLower_ne_of_ne
    {x y z : Sph (d + 1)} (hy : 0 < sphHeight y)
    (hx : sphHeight x < 0) (hzy : z ≠ y) (hzx : z ≠ x) :
    upperCellPunctureLower y hy ⟨z, hzy⟩ ≠ x := by
  intro hout
  by_cases hz : sphHeight z ≤ 0
  · exact hzx ((upperCellPunctureLower_eq_of_height_nonpos
      y hy hzy hz).symm.trans hout)
  · have hz0 : 0 ≤ sphHeight z := le_of_not_ge hz
    have houtheight := congrArg sphHeight hout
    have hheightzero : sphHeight (upperCellPunctureLower y hy ⟨z, hzy⟩) = 0 := by
      change radialProj (upperCellPunctureLowerAmbient y z)
        (Fin.last (d + 1)) = 0
      rw [radialProj, PiLp.smul_apply, smul_eq_mul,
        upperCellPunctureLowerAmbient_last y z hy.ne', min_eq_right hz0,
        mul_zero]
    rw [hheightzero] at houtheight
    linarith

@[simp] theorem upperCellPunctureLower_base
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    (hybase : sphereBasepoint (d + 1) ≠ y) :
    upperCellPunctureLower y hy
      ⟨sphereBasepoint (d + 1), hybase⟩ = sphereBasepoint (d + 1) :=
  upperCellPunctureLower_eq_of_height_nonpos y hy hybase
    (by rw [sphHeight_sphereBasepoint_succ])

/-! ### Raising away from a point in the lower open cell -/

/-- The ambient vector that raises negative height away from a chosen lower-cell point. -/
def lowerCellPunctureRaiseAmbient
    (x : Sph (d + 1)) (u : I) (z : Sph (d + 1)) :
    EuclideanSpace ℝ (Fin (d + 2)) :=
  z.1 - ((u : ℝ) * (min (sphHeight z) 0 / sphHeight x)) • x.1

theorem continuous_lowerCellPunctureRaiseAmbient
    (x : Sph (d + 1)) :
    Continuous fun p : I × Sph (d + 1) =>
      lowerCellPunctureRaiseAmbient x p.1 p.2 := by
  unfold lowerCellPunctureRaiseAmbient
  have hu : Continuous fun p : I × Sph (d + 1) => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : I × Sph (d + 1) => sphHeight p.2 :=
    continuous_sphHeight.comp continuous_snd
  exact (continuous_subtype_val.comp continuous_snd).sub
    ((hu.mul ((hz.min continuous_const).div_const _)).smul continuous_const)

/-- The controlled raising formula changes height from `h` to `h - u * min h 0`. -/
theorem lowerCellPunctureRaiseAmbient_last
    (x : Sph (d + 1)) (hx : sphHeight x ≠ 0)
    (u : I) (z : Sph (d + 1)) :
    lowerCellPunctureRaiseAmbient x u z (Fin.last (d + 1)) =
      sphHeight z - (u : ℝ) * min (sphHeight z) 0 := by
  rw [lowerCellPunctureRaiseAmbient, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  change sphHeight z -
      ((u : ℝ) * (min (sphHeight z) 0 / sphHeight x)) * sphHeight x = _
  rw [mul_assoc, div_mul_cancel₀ _ hx]

/-- With negative chosen height, the raw raising vector can vanish only at full strength at the
chosen point. -/
theorem lowerCellPunctureRaiseAmbient_eq_zero_imp
    (x z : Sph (d + 1)) (hx : sphHeight x < 0) (u : I)
    (hzero : lowerCellPunctureRaiseAmbient x u z = 0) :
    z = x ∧ u = 1 := by
  let a : ℝ := (u : ℝ) * (min (sphHeight z) 0 / sphHeight x)
  have heq : z.1 = a • x.1 := sub_eq_zero.mp hzero
  have ha : 0 ≤ a := by
    apply mul_nonneg u.2.1
    rw [div_nonneg_iff]
    exact Or.inr ⟨min_le_right _ _, hx.le⟩
  have hnorm := congrArg norm heq
  have haone : a = 1 := by
    rw [norm_coe_sph, norm_smul, Real.norm_eq_abs,
      norm_coe_sph, abs_of_nonneg ha] at hnorm
    linarith
  have hzx : z = x := by
    apply Subtype.ext
    rw [heq, haone, one_smul]
  have huval : (u : ℝ) = 1 := by
    have haeq : a = (u : ℝ) := by
      dsimp only [a]
      rw [hzx, min_eq_left hx.le, div_self hx.ne]
      ring
    linarith
  exact ⟨hzx, Subtype.ext huval⟩

theorem lowerCellPunctureRaiseAmbient_ne_zero
    (x z : Sph (d + 1)) (hx : sphHeight x < 0) (u : I)
    (havoid : u = 1 → z ≠ x) :
    lowerCellPunctureRaiseAmbient x u z ≠ 0 := by
  intro hzero
  obtain ⟨hzx, hu⟩ :=
    lowerCellPunctureRaiseAmbient_eq_zero_imp x z hx u hzero
  exact havoid hu hzx

/-- Normalize the controlled lower-puncture raising formula. -/
def lowerCellPunctureRaisePoint
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (u : I) (z : Sph (d + 1)) (havoid : u = 1 → z ≠ x) :
    Sph (d + 1) :=
  radialSpherePoint (lowerCellPunctureRaiseAmbient x u z)
    (lowerCellPunctureRaiseAmbient_ne_zero x z hx u havoid)

@[simp] theorem coe_lowerCellPunctureRaisePoint
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (u : I) (z : Sph (d + 1)) (havoid : u = 1 → z ≠ x) :
    ((lowerCellPunctureRaisePoint x hx u z havoid : Sph (d + 1)) :
      EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj (lowerCellPunctureRaiseAmbient x u z) :=
  rfl

@[simp] theorem lowerCellPunctureRaisePoint_zero
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (z : Sph (d + 1)) (havoid : (0 : I) = 1 → z ≠ x) :
    lowerCellPunctureRaisePoint x hx 0 z havoid = z := by
  apply Subtype.ext
  change radialProj (lowerCellPunctureRaiseAmbient x 0 z) = z.1
  have hamb : lowerCellPunctureRaiseAmbient x 0 z = z.1 := by
    rw [lowerCellPunctureRaiseAmbient]
    norm_num
  rw [hamb, radialProj_of_norm_eq_one (norm_coe_sph z)]

/-- The raising operation preserves the lower cap at every control value. -/
theorem lowerCellPunctureRaisePoint_mem_lowerCap
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (u : I) {z : Sph (d + 1)} (hz : z ∈ sphLowerCap d)
    (havoid : u = 1 → z ≠ x) :
    lowerCellPunctureRaisePoint x hx u z havoid ∈ sphLowerCap d := by
  rw [mem_sphLowerCap] at hz ⊢
  change radialProj (lowerCellPunctureRaiseAmbient x u z)
    (Fin.last (d + 1)) ≤ 1 / 3
  by_cases hz0 : sphHeight z ≤ 0
  · apply (radialProj_last_nonpos ?_).trans (by norm_num)
    rw [lowerCellPunctureRaiseAmbient_last x hx.ne u z,
      min_eq_left hz0]
    have hmul := mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr u.2.2) hz0
    nlinarith
  · have hz0' : 0 ≤ sphHeight z := le_of_not_ge hz0
    have hamb : lowerCellPunctureRaiseAmbient x u z = z.1 := by
      rw [lowerCellPunctureRaiseAmbient, min_eq_right hz0',
        zero_div, mul_zero, zero_smul, sub_zero]
    rw [hamb, radialProj_of_norm_eq_one (norm_coe_sph z)]
    exact hz

/-- At full strength the raising operation has nonnegative height. -/
theorem lowerCellPunctureRaisePoint_height_nonneg_one
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    {z : Sph (d + 1)} (hzx : z ≠ x) :
    0 ≤ sphHeight
      (lowerCellPunctureRaisePoint x hx 1 z (fun _ => hzx)) := by
  change 0 ≤ radialProj (lowerCellPunctureRaiseAmbient x 1 z)
    (Fin.last (d + 1))
  apply radialProj_last_nonneg
  rw [lowerCellPunctureRaiseAmbient_last x hx.ne 1 z]
  by_cases hz0 : sphHeight z ≤ 0
  · rw [min_eq_left hz0]
    norm_num
  · rw [min_eq_right (le_of_not_ge hz0)]
    simpa using le_of_not_ge hz0

/-- At full strength the raising operation lands in the upper cap. -/
theorem lowerCellPunctureRaisePoint_mem_upperCap_one
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    {z : Sph (d + 1)} (hzx : z ≠ x) :
    lowerCellPunctureRaisePoint x hx 1 z (fun _ => hzx) ∈ sphUpperCap d := by
  rw [mem_sphUpperCap]
  exact le_trans (by norm_num : -(1 / 3 : ℝ) ≤ 0)
    (lowerCellPunctureRaisePoint_height_nonneg_one x hx hzx)

/-- Nonnegative-height points are fixed by every stage of the raising operation. -/
theorem lowerCellPunctureRaisePoint_eq_of_height_nonneg
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (u : I) {z : Sph (d + 1)} (hz : 0 ≤ sphHeight z)
    (havoid : u = 1 → z ≠ x) :
    lowerCellPunctureRaisePoint x hx u z havoid = z := by
  apply Subtype.ext
  change radialProj (lowerCellPunctureRaiseAmbient x u z) = z.1
  have hamb : lowerCellPunctureRaiseAmbient x u z = z.1 := by
    rw [lowerCellPunctureRaiseAmbient, min_eq_right hz,
      zero_div, mul_zero, zero_smul, sub_zero]
  rw [hamb, radialProj_of_norm_eq_one (norm_coe_sph z)]

/-- Raising away from `x` cannot create a hit of a positive-height point `y`. -/
theorem lowerCellPunctureRaisePoint_ne_of_ne
    {x y z : Sph (d + 1)} (hx : sphHeight x < 0)
    (hy : 0 < sphHeight y) (u : I) (hzy : z ≠ y)
    (havoid : u = 1 → z ≠ x) :
    lowerCellPunctureRaisePoint x hx u z havoid ≠ y := by
  intro hout
  by_cases hz : sphHeight z ≤ 0
  · have hraw : lowerCellPunctureRaiseAmbient x u z
        (Fin.last (d + 1)) ≤ 0 := by
      rw [lowerCellPunctureRaiseAmbient_last x hx.ne u z,
        min_eq_left hz]
      have hmul := mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr u.2.2) hz
      nlinarith
    have houtnonpos :
        sphHeight (lowerCellPunctureRaisePoint x hx u z havoid) ≤ 0 := by
      change radialProj (lowerCellPunctureRaiseAmbient x u z)
        (Fin.last (d + 1)) ≤ 0
      exact radialProj_last_nonpos hraw
    rw [hout] at houtnonpos
    linarith
  · have hznonneg : 0 ≤ sphHeight z := le_of_not_ge hz
    exact hzy ((lowerCellPunctureRaisePoint_eq_of_height_nonneg
      x hx u hznonneg havoid).symm.trans hout)

@[simp] theorem lowerCellPunctureRaisePoint_base
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (u : I) (havoid : u = 1 → sphereBasepoint (d + 1) ≠ x) :
    lowerCellPunctureRaisePoint x hx u (sphereBasepoint (d + 1)) havoid =
      sphereBasepoint (d + 1) :=
  lowerCellPunctureRaisePoint_eq_of_height_nonneg x hx u
    (by rw [sphHeight_sphereBasepoint_succ]) havoid

end Submission
