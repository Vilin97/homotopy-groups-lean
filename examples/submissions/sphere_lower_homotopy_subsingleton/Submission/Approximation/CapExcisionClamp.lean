/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.SpatialJarGeneralPosition

/-!
# Clamping north-avoiding sphere representatives through cap excision

Removing the north pole from `Sph (d+1)` permits an explicit deformation into the enlarged lower
cap.  We keep the equatorial vector fixed, replace the last coordinate `h` by
`min h (‖equator‖ / 3)`, and radially normalize.  The raw vector vanishes exactly at the north
pole.  The deformation fixes the distinguished equatorial basepoint, preserves both enlarged
caps, sends upper-cap points into the belt at its endpoint, and therefore respects all relative
loop conditions used by suspension cap excision.

The final section turns this geometry into quotient-level criteria.  A target representative
avoiding the north pole has an explicit preimage under the cap-excision map.  Likewise, a
north-avoiding target homotopy between included source representatives clamps to a homotopy in
the source pair.  Thus stable cap excision is reduced to precise representative and homotopy
avoidance statements, with no remaining quotient or cap-deformation bookkeeping.

## Main results

* `Submission.lowerCapClampHomotopy_mem_upperCap`
* `Submission.lowerCapClampHomotopy_mem_lowerCap`
* `Submission.capExcisionLiftRelGenLoop_homotopic`
* `Submission.sphereSuspensionExcisionHomAt_surjective_of_avoiding_north`
* `Submission.sphereSuspensionExcisionHomAt_injective_of_homotopies_avoiding_north`
* `Submission.sphereSuspensionExcisionHomAt_bijective_of_avoiding_north`
-/

open HomotopyGroups
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {d : ℕ}

/-- The north pole used by the punctured-sphere cap clamp. -/
noncomputable def sphNorthPole (d : ℕ) : Sph (d + 1) :=
  sphPole d 1 (by norm_num)

@[simp] theorem sphHeight_sphNorthPole (d : ℕ) :
    sphHeight (sphNorthPole d) = 1 := by
  simp [sphNorthPole]

@[simp] theorem sphEquator_sphNorthPole (d : ℕ) :
    sphEquator (sphNorthPole d) = 0 := by
  simp [sphNorthPole]

/-- The raw last coordinate used to clamp the punctured sphere into the lower cap. -/
noncomputable def lowerCapClampHeight (z : Sph (d + 1)) : ℝ :=
  min (sphHeight z) (‖sphEquator z‖ / 3)

theorem continuous_lowerCapClampHeight :
    Continuous (lowerCapClampHeight (d := d)) := by
  exact continuous_sphHeight.min (continuous_sphEquator.norm.div_const 3)

/-- A globally continuous ambient vector which vanishes only at the north pole. -/
noncomputable def lowerCapClampAmbient (z : Sph (d + 1)) :
    EuclideanSpace ℝ (Fin (d + 2)) :=
  snocLp (sphEquator z) (lowerCapClampHeight z)

theorem continuous_lowerCapClampAmbient :
    Continuous (lowerCapClampAmbient (d := d)) := by
  exact continuous_snocLp.comp
    (continuous_sphEquator.prodMk continuous_lowerCapClampHeight)

@[simp] theorem lowerCapClampAmbient_sphNorthPole (d : ℕ) :
    lowerCapClampAmbient (sphNorthPole d) = 0 := by
  apply PiLp.ext
  intro i
  induction i using Fin.lastCases with
  | last => simp [lowerCapClampAmbient, lowerCapClampHeight, snocLp_last]
  | cast j => simp [lowerCapClampAmbient, lowerCapClampHeight, snocLp_castSucc]

theorem lowerCapClampAmbient_eq_zero_iff (z : Sph (d + 1)) :
    lowerCapClampAmbient z = 0 ↔ z = sphNorthPole d := by
  constructor
  · intro hz
    have heq : sphEquator z = 0 := by
      apply PiLp.ext
      intro i
      have := congrArg (fun v : EuclideanSpace ℝ (Fin (d + 2)) =>
        v i.castSucc) hz
      simpa [lowerCapClampAmbient] using this
    have hlast : lowerCapClampHeight z = 0 := by
      have := congrArg (fun v : EuclideanSpace ℝ (Fin (d + 2)) =>
        v (Fin.last (d + 1))) hz
      simpa [lowerCapClampAmbient] using this
    have hsq : sphHeight z ^ 2 = 1 := by
      have := norm_sphEquator_sq z
      rw [heq, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at this
      linarith
    have hheight : sphHeight z = 1 := by
      have hor := sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans (one_pow 2).symm)
      rcases hor with h | h
      · exact h
      · have : lowerCapClampHeight z = -1 := by
          rw [lowerCapClampHeight, heq, norm_zero, h]
          norm_num
        linarith
    apply Subtype.ext
    rw [← snocLp_sphEquator_sphHeight z]
    change snocLp (sphEquator z) (sphHeight z) = snocLp 0 1
    rw [heq, hheight]
  · rintro rfl
    exact lowerCapClampAmbient_sphNorthPole d

theorem lowerCapClampAmbient_ne_zero {z : Sph (d + 1)}
    (hz : z ≠ sphNorthPole d) : lowerCapClampAmbient z ≠ 0 :=
  (lowerCapClampAmbient_eq_zero_iff z).not.mpr hz

/-- The punctured sphere, with the north pole removed. -/
abbrev SphNorthCompl (d : ℕ) := {z : Sph (d + 1) // z ≠ sphNorthPole d}

/-- Clamp the punctured sphere radially into the enlarged lower cap. -/
noncomputable def lowerCapClamp : C(SphNorthCompl d, Sph (d + 1)) where
  toFun z := ⟨radialProj (lowerCapClampAmbient z.1),
    mem_sphere_zero_iff_norm.mpr (norm_radialProj
      (lowerCapClampAmbient_ne_zero z.2))⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_radialProj
      (continuous_lowerCapClampAmbient.comp continuous_subtype_val)
      (fun z => lowerCapClampAmbient_ne_zero z.2)) _

@[simp] theorem coe_lowerCapClamp (z : SphNorthCompl d) :
    ((lowerCapClamp z : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj (lowerCapClampAmbient z.1) :=
  rfl

/-- The raw straight-line deformation from the identity to the cap clamp.  The equatorial
component is fixed and only the last coordinate is lowered. -/
noncomputable def lowerCapClampHomotopyAmbient
    (p : I × Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2)) :=
  snocLp (sphEquator p.2)
    ((1 - (p.1 : ℝ)) * sphHeight p.2 +
      (p.1 : ℝ) * lowerCapClampHeight p.2)

theorem continuous_lowerCapClampHomotopyAmbient :
    Continuous (lowerCapClampHomotopyAmbient (d := d)) := by
  change Continuous fun p : I × Sph (d + 1) =>
    snocLp (sphEquator p.2)
      ((1 - (p.1 : ℝ)) * sphHeight p.2 +
        (p.1 : ℝ) * lowerCapClampHeight p.2)
  have hu : Continuous fun p : I × Sph (d + 1) => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hh : Continuous fun p : I × Sph (d + 1) => sphHeight p.2 :=
    continuous_sphHeight.comp continuous_snd
  have hr : Continuous fun p : I × Sph (d + 1) => lowerCapClampHeight p.2 :=
    continuous_lowerCapClampHeight.comp continuous_snd
  exact continuous_snocLp.comp
    ((continuous_sphEquator.comp continuous_snd).prodMk
      ((continuous_const.sub hu).mul hh |>.add (hu.mul hr)))

@[simp] theorem lowerCapClampHomotopyAmbient_zero (z : Sph (d + 1)) :
    lowerCapClampHomotopyAmbient (0, z) = z.1 := by
  simp [lowerCapClampHomotopyAmbient, snocLp_sphEquator_sphHeight]

@[simp] theorem lowerCapClampHomotopyAmbient_one (z : Sph (d + 1)) :
    lowerCapClampHomotopyAmbient (1, z) = lowerCapClampAmbient z := by
  simp [lowerCapClampHomotopyAmbient, lowerCapClampAmbient]

theorem lowerCapClampHomotopyAmbient_eq_zero_imp
    (u : I) (z : Sph (d + 1))
    (hz : lowerCapClampHomotopyAmbient (u, z) = 0) :
    z = sphNorthPole d := by
  have heq : sphEquator z = 0 := by
    apply PiLp.ext
    intro i
    have := congrArg (fun v : EuclideanSpace ℝ (Fin (d + 2)) =>
      v i.castSucc) hz
    simpa [lowerCapClampHomotopyAmbient] using this
  have hlast :
      (1 - (u : ℝ)) * sphHeight z +
        (u : ℝ) * lowerCapClampHeight z = 0 := by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin (d + 2)) =>
      v (Fin.last (d + 1))) hz
    simpa [lowerCapClampHomotopyAmbient] using this
  have hsq : sphHeight z ^ 2 = 1 := by
    have := norm_sphEquator_sq z
    rw [heq, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at this
    linarith
  have hheight : sphHeight z = 1 := by
    have hor := sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans (one_pow 2).symm)
    rcases hor with h | h
    · exact h
    · have hraw : lowerCapClampHeight z = -1 := by
        rw [lowerCapClampHeight, heq, norm_zero, h]
        norm_num
      rw [h, hraw] at hlast
      linarith
  apply Subtype.ext
  rw [← snocLp_sphEquator_sphHeight z]
  change snocLp (sphEquator z) (sphHeight z) = snocLp 0 1
  rw [heq, hheight]

theorem lowerCapClampHomotopyAmbient_ne_zero
    (u : I) {z : Sph (d + 1)} (hz : z ≠ sphNorthPole d) :
    lowerCapClampHomotopyAmbient (u, z) ≠ 0 :=
  fun hzero => hz (lowerCapClampHomotopyAmbient_eq_zero_imp u z hzero)

/-- Deformation of the north-punctured sphere from the identity to the lower-cap clamp. -/
noncomputable def lowerCapClampHomotopy :
    C(I × SphNorthCompl d, Sph (d + 1)) where
  toFun p := ⟨radialProj (lowerCapClampHomotopyAmbient (p.1, p.2.1)),
    mem_sphere_zero_iff_norm.mpr (norm_radialProj
      (lowerCapClampHomotopyAmbient_ne_zero p.1 p.2.2))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_radialProj
    · exact continuous_lowerCapClampHomotopyAmbient.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    · intro p
      exact lowerCapClampHomotopyAmbient_ne_zero p.1 p.2.2

@[simp] theorem lowerCapClampHomotopy_zero (z : SphNorthCompl d) :
    lowerCapClampHomotopy (0, z) = z.1 := by
  apply Subtype.ext
  change radialProj (lowerCapClampHomotopyAmbient (0, z.1)) = z.1.1
  rw [lowerCapClampHomotopyAmbient_zero,
    radialProj_of_norm_eq_one (norm_coe_sph z.1)]

@[simp] theorem lowerCapClampHomotopy_one (z : SphNorthCompl d) :
    lowerCapClampHomotopy (1, z) = lowerCapClamp z := by
  apply Subtype.ext
  change radialProj (lowerCapClampHomotopyAmbient (1, z.1)) =
    radialProj (lowerCapClampAmbient z.1)
  rw [lowerCapClampHomotopyAmbient_one]

theorem lowerCapClampHeight_eq_height_of_le
    {z : Sph (d + 1)} (hz : sphHeight z ≤ ‖sphEquator z‖ / 3) :
    lowerCapClampHeight z = sphHeight z :=
  min_eq_left hz

theorem lowerCapClampAmbient_eq_of_le
    {z : Sph (d + 1)} (hz : sphHeight z ≤ ‖sphEquator z‖ / 3) :
    lowerCapClampAmbient z = z.1 := by
  rw [lowerCapClampAmbient, lowerCapClampHeight_eq_height_of_le hz,
    snocLp_sphEquator_sphHeight]

theorem lowerCapClampHomotopyAmbient_eq_of_le
    (u : I) {z : Sph (d + 1)} (hz : sphHeight z ≤ ‖sphEquator z‖ / 3) :
    lowerCapClampHomotopyAmbient (u, z) = z.1 := by
  rw [lowerCapClampHomotopyAmbient, lowerCapClampHeight_eq_height_of_le hz]
  have hlast :
      (1 - (u : ℝ)) * sphHeight z + (u : ℝ) * sphHeight z =
        sphHeight z := by ring
  rw [hlast, snocLp_sphEquator_sphHeight]

theorem sphHeight_le_equatorNorm_div_three_of_nonpos
    {z : Sph (d + 1)} (hz : sphHeight z ≤ 0) :
    sphHeight z ≤ ‖sphEquator z‖ / 3 := by
  exact hz.trans (div_nonneg (norm_nonneg _) (by norm_num))

theorem lowerCapClampHomotopy_eq_of_height_nonpos
    (u : I) {z : Sph (d + 1)} (hz : sphHeight z ≤ 0)
    (hnorth : z ≠ sphNorthPole d) :
    lowerCapClampHomotopy (u, ⟨z, hnorth⟩) = z := by
  apply Subtype.ext
  change radialProj (lowerCapClampHomotopyAmbient (u, z)) = z.1
  rw [lowerCapClampHomotopyAmbient_eq_of_le u
    (sphHeight_le_equatorNorm_div_three_of_nonpos hz),
    radialProj_of_norm_eq_one (norm_coe_sph z)]

theorem sphereBasepoint_ne_sphNorthPole (d : ℕ) :
    sphereBasepoint (d + 1) ≠ sphNorthPole d := by
  intro h
  have := congrArg sphHeight h
  rw [sphHeight_sphereBasepoint_succ, sphHeight_sphNorthPole] at this
  norm_num at this

@[simp] theorem lowerCapClampHomotopy_base (d : ℕ) (u : I) :
    lowerCapClampHomotopy
      (u, ⟨sphereBasepoint (d + 1), sphereBasepoint_ne_sphNorthPole d⟩) =
        sphereBasepoint (d + 1) := by
  exact lowerCapClampHomotopy_eq_of_height_nonpos u
    (by rw [sphHeight_sphereBasepoint_succ])
    (sphereBasepoint_ne_sphNorthPole d)

@[simp] theorem lowerCapClamp_base (d : ℕ) :
    lowerCapClamp
      ⟨sphereBasepoint (d + 1), sphereBasepoint_ne_sphNorthPole d⟩ =
        sphereBasepoint (d + 1) := by
  rw [← lowerCapClampHomotopy_one]
  exact lowerCapClampHomotopy_base d 1

/-- A radial vector whose last coordinate is at most one third of the equatorial norm lands in
the enlarged lower cap. -/
theorem radialProj_snocLp_last_le_third
    {e : EuclideanSpace ℝ (Fin (d + 1))} {a : ℝ}
    (hne : snocLp e a ≠ 0) (ha : a ≤ ‖e‖ / 3) :
    radialProj (snocLp e a) (Fin.last (d + 1)) ≤ 1 / 3 := by
  rw [radialProj, PiLp.smul_apply, smul_eq_mul, snocLp_last]
  by_cases ha0 : a ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos
      (inv_nonneg.mpr (norm_nonneg _)) ha0).trans (by norm_num)
  · have ha0' : 0 < a := lt_of_not_ge ha0
    have hnormpos : 0 < ‖snocLp e a‖ := norm_pos_iff.mpr hne
    have hnormsq := norm_snocLp_sq e a
    have her : ‖e‖ ≤ ‖snocLp e a‖ := by
      apply le_of_sq_le_sq
      · nlinarith [sq_nonneg a]
      · exact norm_nonneg _
    have hthree : 3 * a ≤ ‖e‖ := by linarith
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ hnormpos).2
    nlinarith

/-- The punctured-sphere clamp lands in the enlarged lower cap. -/
theorem lowerCapClamp_mem_lowerCap (z : SphNorthCompl d) :
    lowerCapClamp z ∈ sphLowerCap d := by
  rw [mem_sphLowerCap]
  change radialProj (lowerCapClampAmbient z.1) (Fin.last (d + 1)) ≤ 1 / 3
  exact radialProj_snocLp_last_le_third
    (lowerCapClampAmbient_ne_zero z.2) (min_le_right _ _)

/-- During the clamp deformation, an upper-cap point stays in the upper cap. -/
theorem lowerCapClampHomotopy_mem_upperCap
    (u : I) {z : Sph (d + 1)} (hz : z ∈ sphUpperCap d)
    (hnorth : z ≠ sphNorthPole d) :
    lowerCapClampHomotopy (u, ⟨z, hnorth⟩) ∈ sphUpperCap d := by
  rw [mem_sphUpperCap] at hz ⊢
  by_cases hle : sphHeight z ≤ ‖sphEquator z‖ / 3
  · change -(1 / 3 : ℝ) ≤ radialProj
      (lowerCapClampHomotopyAmbient (u, z)) (Fin.last (d + 1))
    rw [lowerCapClampHomotopyAmbient_eq_of_le u hle,
      radialProj_of_norm_eq_one (norm_coe_sph z)]
    exact hz
  · change -(1 / 3 : ℝ) ≤ radialProj
      (lowerCapClampHomotopyAmbient (u, z)) (Fin.last (d + 1))
    apply le_trans (by norm_num : -(1 / 3 : ℝ) ≤ 0)
    apply radialProj_last_nonneg
    rw [lowerCapClampHomotopyAmbient, snocLp_last,
      lowerCapClampHeight, min_eq_right (le_of_not_ge hle)]
    have hr : 0 ≤ ‖sphEquator z‖ / 3 :=
      div_nonneg (norm_nonneg _) (by norm_num)
    have hh : 0 ≤ sphHeight z := le_trans hr (le_of_not_ge hle)
    have hu0 : 0 ≤ (u : ℝ) := u.2.1
    have hu1 : (u : ℝ) ≤ 1 := u.2.2
    positivity

/-- An upper-cap point is sent into the belt by the final clamp. -/
theorem lowerCapClamp_mem_belt_of_mem_upperCap
    {z : Sph (d + 1)} (hz : z ∈ sphUpperCap d)
    (hnorth : z ≠ sphNorthPole d) :
    lowerCapClamp ⟨z, hnorth⟩ ∈ sphBelt d := by
  rw [sphBelt, Set.mem_inter_iff]
  exact ⟨lowerCapClamp_mem_lowerCap _,
    by rw [← lowerCapClampHomotopy_one]
       exact lowerCapClampHomotopy_mem_upperCap 1 hz hnorth⟩

/-- Lowering the last coordinate of a point already in the lower cap, while fixing its
equatorial coordinates and radially normalizing, stays in the lower cap. -/
theorem radialProj_snocLp_last_le_third_of_le_sphHeight
    (z : Sph (d + 1)) {a : ℝ}
    (hne : snocLp (sphEquator z) a ≠ 0)
    (ha : a ≤ sphHeight z) (hz : sphHeight z ≤ 1 / 3) :
    radialProj (snocLp (sphEquator z) a) (Fin.last (d + 1)) ≤ 1 / 3 := by
  rw [radialProj, PiLp.smul_apply, smul_eq_mul, snocLp_last]
  by_cases ha0 : a ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos
      (inv_nonneg.mpr (norm_nonneg _)) ha0).trans (by norm_num)
  · have ha0' : 0 < a := lt_of_not_ge ha0
    have hh0 : 0 < sphHeight z := ha0'.trans_le ha
    have ha_sq : a * a ≤ sphHeight z * sphHeight z :=
      mul_self_le_mul_self (le_of_lt ha0') ha
    have hh_sq : sphHeight z * sphHeight z ≤ (1 / 3 : ℝ) * (1 / 3) :=
      mul_self_le_mul_self (le_of_lt hh0) hz
    have heq_sq := norm_sphEquator_sq z
    have hv_sq := norm_snocLp_sq (sphEquator z) a
    have hthree : 3 * a ≤ ‖snocLp (sphEquator z) a‖ := by
      apply le_of_sq_le_sq
      · nlinarith
      · exact norm_nonneg _
    have hnormpos : 0 < ‖snocLp (sphEquator z) a‖ := norm_pos_iff.mpr hne
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ hnormpos).2
    nlinarith

/-- During the clamp deformation, a lower-cap point stays in the lower cap. -/
theorem lowerCapClampHomotopy_mem_lowerCap
    (u : I) {z : Sph (d + 1)} (hz : z ∈ sphLowerCap d)
    (hnorth : z ≠ sphNorthPole d) :
    lowerCapClampHomotopy (u, ⟨z, hnorth⟩) ∈ sphLowerCap d := by
  rw [mem_sphLowerCap] at hz ⊢
  let a := (1 - (u : ℝ)) * sphHeight z +
    (u : ℝ) * lowerCapClampHeight z
  have hraw : lowerCapClampHeight z ≤ sphHeight z := min_le_left _ _
  have hmul : (u : ℝ) * (lowerCapClampHeight z - sphHeight z) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos u.2.1 (sub_nonpos.mpr hraw)
  have ha : a ≤ sphHeight z := by
    dsimp only [a]
    nlinarith
  change radialProj (snocLp (sphEquator z) a) (Fin.last (d + 1)) ≤ 1 / 3
  apply radialProj_snocLp_last_le_third_of_le_sphHeight z
  · exact lowerCapClampHomotopyAmbient_ne_zero u hnorth
  · exact ha
  · exact hz

/-- During the clamp deformation, a belt point stays in the belt. -/
theorem lowerCapClampHomotopy_mem_belt
    (u : I) {z : Sph (d + 1)} (hz : z ∈ sphBelt d)
    (hnorth : z ≠ sphNorthPole d) :
    lowerCapClampHomotopy (u, ⟨z, hnorth⟩) ∈ sphBelt d := by
  rw [sphBelt, Set.mem_inter_iff] at hz ⊢
  exact ⟨lowerCapClampHomotopy_mem_lowerCap u hz.1 hnorth,
    lowerCapClampHomotopy_mem_upperCap u hz.2 hnorth⟩

/-! ### Lifting north-avoiding relative representatives through cap excision -/

variable {n : ℕ}

/-- A relative sphere representative avoiding the north pole clamps to a representative in the
lower-cap/overlap pair. -/
noncomputable def capExcisionLiftRelGenLoop
    (p : RelGenLoop n (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (havoid : ∀ y, p.val y ≠ sphNorthPole d) :
    RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d) (sphCapOverlapBase d) where
  val :=
    ⟨fun y => ⟨lowerCapClamp ⟨p.val y, havoid y⟩,
        lowerCapClamp_mem_lowerCap ⟨p.val y, havoid y⟩⟩,
      Continuous.subtype_mk
        (lowerCapClamp.continuous.comp
          (Continuous.subtype_mk p.val.continuous (fun y => havoid y))) _⟩
  property := by
    constructor
    · intro y hy
      exact (lowerCapClamp_mem_belt_of_mem_upperCap
        (p.property.1 y hy) (havoid y)).2
    · intro y hy
      apply Subtype.ext
      change lowerCapClamp ⟨p.val y, havoid y⟩ = sphereBasepoint (d + 1)
      have hp := p.property.2 y hy
      change p.val y = sphereBasepoint (d + 1) at hp
      have hp' : (⟨p.val y, havoid y⟩ : SphNorthCompl d) =
          ⟨sphereBasepoint (d + 1), sphereBasepoint_ne_sphNorthPole d⟩ :=
        Subtype.ext hp
      rw [hp', lowerCapClamp_base]

@[simp] theorem capExcisionLiftRelGenLoop_apply
    (p : RelGenLoop n (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (havoid : ∀ y, p.val y ≠ sphNorthPole d) (y : I^ Fin n) :
    ((capExcisionLiftRelGenLoop p havoid).val y : sphLowerCap d) =
      lowerCapClamp ⟨p.val y, havoid y⟩ :=
  rfl

/-- Clamping a north-avoiding representative is a relative homotopy in the target pair from the
original representative to the image of its cap-excision lift. -/
theorem capExcisionLiftRelGenLoop_homotopic
    (p : RelGenLoop n (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (havoid : ∀ y, p.val y ≠ sphNorthPole d) :
    RelGenLoop.Homotopic p
      (RelGenLoop.map (sphCapInclusionPairMap d)
        (capExcisionLiftRelGenLoop p havoid)) := by
  refine ⟨⟨⟨fun sy =>
      lowerCapClampHomotopy (sy.1, ⟨p.val sy.2, havoid sy.2⟩), ?_⟩,
    ?_, ?_⟩, ?_⟩
  · exact lowerCapClampHomotopy.continuous.comp
      (continuous_fst.prodMk
        (Continuous.subtype_mk (p.val.continuous.comp continuous_snd)
          (fun sy => havoid sy.2)))
  · intro y
    exact lowerCapClampHomotopy_zero ⟨p.val y, havoid y⟩
  · intro y
    change lowerCapClampHomotopy (1, ⟨p.val y, havoid y⟩) =
      lowerCapClamp ⟨p.val y, havoid y⟩
    exact lowerCapClampHomotopy_one ⟨p.val y, havoid y⟩
  · intro u
    constructor
    · intro y hy
      exact lowerCapClampHomotopy_mem_upperCap u (p.property.1 y hy) (havoid y)
    · intro y hy
      change lowerCapClampHomotopy (u, ⟨p.val y, havoid y⟩) =
        sphereBasepoint (d + 1)
      have hp := p.property.2 y hy
      change p.val y = sphereBasepoint (d + 1) at hp
      have hp' : (⟨p.val y, havoid y⟩ : SphNorthCompl d) =
          ⟨sphereBasepoint (d + 1), sphereBasepoint_ne_sphNorthPole d⟩ :=
        Subtype.ext hp
      rw [hp', lowerCapClampHomotopy_base]

/-- On quotient classes, the image of the explicit cap lift is the original north-avoiding
relative class. -/
theorem sphereSuspensionExcisionHomAt_capExcisionLiftRelGenLoop
    (q : ℕ)
    (p : RelGenLoop (q + 2) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (havoid : ∀ y, p.val y ≠ sphNorthPole d) :
    sphereSuspensionExcisionHomAt d q
        (⟦capExcisionLiftRelGenLoop p havoid⟧ :
          π_rel (q + 2) (sphLowerCap d) (sphCapOverlapInLower d)
            (sphCapOverlapBase d)) =
      (⟦p⟧ : π_rel (q + 2) (Sph (d + 1)) (sphUpperCap d)
        (sphUpperCapBase d)) := by
  change (⟦RelGenLoop.map (sphCapInclusionPairMap d)
    (capExcisionLiftRelGenLoop p havoid)⟧ :
      π_rel (q + 2) (Sph (d + 1)) (sphUpperCap d)
        (sphUpperCapBase d)) = ⟦p⟧
  exact Quotient.sound (capExcisionLiftRelGenLoop_homotopic p havoid).symm

/-- If every target representative can be moved off the north pole, cap excision is
surjective.  This isolates the geometric input needed for representative-level surjectivity. -/
theorem sphereSuspensionExcisionHomAt_surjective_of_avoiding_north
    (q : ℕ)
    (havoid : ∀ p : RelGenLoop (q + 2) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d),
      ∃ p' : RelGenLoop (q + 2) (Sph (d + 1))
          (sphUpperCap d) (sphUpperCapBase d),
        RelGenLoop.Homotopic p p' ∧ ∀ y, p'.val y ≠ sphNorthPole d) :
    Function.Surjective (sphereSuspensionExcisionHomAt d q) := by
  intro x
  induction x using Quotient.inductionOn with
  | _ p =>
      obtain ⟨p', hpp', hp'avoid⟩ := havoid p
      refine ⟨(⟦capExcisionLiftRelGenLoop p' hp'avoid⟧ :
        π_rel (q + 2) (sphLowerCap d) (sphCapOverlapInLower d)
          (sphCapOverlapBase d)), ?_⟩
      rw [sphereSuspensionExcisionHomAt_capExcisionLiftRelGenLoop]
      exact Quotient.sound hpp'.symm

/-- A point of the lower cap cannot be the north pole. -/
theorem sphLowerCap_coe_ne_sphNorthPole (z : sphLowerCap d) :
    (z.1 : Sph (d + 1)) ≠ sphNorthPole d := by
  intro hz
  have hheight := z.2
  rw [mem_sphLowerCap, hz, sphHeight_sphNorthPole] at hheight
  norm_num at hheight

/-- Clamp a source representative after including it into the sphere. -/
noncomputable def capExcisionClampSourceRelGenLoop
    (p : RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d)) :
    RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d) :=
  capExcisionLiftRelGenLoop
    (RelGenLoop.map (sphCapInclusionPairMap d) p)
    (fun y => sphLowerCap_coe_ne_sphNorthPole (p.val y))

/-- The cap clamp deformation restricted to the lower cap. -/
noncomputable def lowerCapClampSourceDeformation :
    C(I × sphLowerCap d, sphLowerCap d) where
  toFun uz :=
    ⟨lowerCapClampHomotopy
        (uz.1, ⟨uz.2.1, sphLowerCap_coe_ne_sphNorthPole uz.2⟩),
      lowerCapClampHomotopy_mem_lowerCap uz.1 uz.2.2
        (sphLowerCap_coe_ne_sphNorthPole uz.2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact lowerCapClampHomotopy.continuous.comp
      (continuous_fst.prodMk
        (Continuous.subtype_mk
          (continuous_subtype_val.comp continuous_snd)
          (fun uz => sphLowerCap_coe_ne_sphNorthPole uz.2)))

@[simp] theorem lowerCapClampSourceDeformation_zero (z : sphLowerCap d) :
    lowerCapClampSourceDeformation (0, z) = z := by
  apply Subtype.ext
  change lowerCapClampHomotopy
    (0, ⟨z.1, sphLowerCap_coe_ne_sphNorthPole z⟩) = z.1
  exact lowerCapClampHomotopy_zero _

@[simp] theorem lowerCapClampSourceDeformation_one (z : sphLowerCap d) :
    lowerCapClampSourceDeformation (1, z) =
      ⟨lowerCapClamp ⟨z.1, sphLowerCap_coe_ne_sphNorthPole z⟩,
        lowerCapClamp_mem_lowerCap _⟩ := by
  apply Subtype.ext
  change lowerCapClampHomotopy
    (1, ⟨z.1, sphLowerCap_coe_ne_sphNorthPole z⟩) =
      lowerCapClamp ⟨z.1, sphLowerCap_coe_ne_sphNorthPole z⟩
  exact lowerCapClampHomotopy_one _

theorem lowerCapClampSourceDeformation_mem_overlap
    (u : I) {z : sphLowerCap d} (hz : z ∈ sphCapOverlapInLower d) :
    lowerCapClampSourceDeformation (u, z) ∈ sphCapOverlapInLower d := by
  have hbelt : z.1 ∈ sphBelt d := ⟨z.2, hz⟩
  exact (lowerCapClampHomotopy_mem_belt u hbelt
    (sphLowerCap_coe_ne_sphNorthPole z)).2

@[simp] theorem lowerCapClampSourceDeformation_base (d : ℕ) (u : I) :
    lowerCapClampSourceDeformation (u, sphLowerCapBase d) = sphLowerCapBase d := by
  apply Subtype.ext
  exact lowerCapClampHomotopy_base d u

/-- A source representative is relatively homotopic, inside the lower-cap/overlap pair, to its
clamped version. -/
theorem capExcisionClampSourceRelGenLoop_homotopic
    (p : RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d)) :
    RelGenLoop.Homotopic p (capExcisionClampSourceRelGenLoop p) := by
  refine ⟨⟨⟨fun sy => lowerCapClampSourceDeformation (sy.1, p.val sy.2),
    lowerCapClampSourceDeformation.continuous.comp
      (continuous_fst.prodMk (p.val.continuous.comp continuous_snd))⟩,
    ?_, ?_⟩, ?_⟩
  · intro y
    exact lowerCapClampSourceDeformation_zero (p.val y)
  · intro y
    exact lowerCapClampSourceDeformation_one (p.val y)
  · intro u
    constructor
    · intro y hy
      exact lowerCapClampSourceDeformation_mem_overlap u (p.property.1 y hy)
    · intro y hy
      change lowerCapClampSourceDeformation (u, p.val y) = sphLowerCapBase d
      rw [p.property.2 y hy]
      change lowerCapClampSourceDeformation (u, sphLowerCapBase d) = sphLowerCapBase d
      exact lowerCapClampSourceDeformation_base d u

/-- Clamping an entire north-avoiding target homotopy produces a homotopy in the source
lower-cap/overlap pair. -/
theorem capExcisionClampSourceRelGenLoop_homotopic_of_targetHomotopy_avoids_north
    {p q : RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d)}
    (H : ContinuousMap.HomotopyWith
      (RelGenLoop.map (sphCapInclusionPairMap d) p).val
      (RelGenLoop.map (sphCapInclusionPairMap d) q).val
      (fun f => f ∈ RelGenLoop n (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d)))
    (havoid : ∀ sy, H.toHomotopy sy ≠ sphNorthPole d) :
    RelGenLoop.Homotopic (capExcisionClampSourceRelGenLoop p)
      (capExcisionClampSourceRelGenLoop q) := by
  refine ⟨⟨⟨fun sy =>
      ⟨lowerCapClamp ⟨H.toHomotopy sy, havoid sy⟩,
        lowerCapClamp_mem_lowerCap ⟨H.toHomotopy sy, havoid sy⟩⟩, ?_⟩,
    ?_, ?_⟩, ?_⟩
  · apply Continuous.subtype_mk
    exact lowerCapClamp.continuous.comp
      (Continuous.subtype_mk H.continuous (fun sy => havoid sy))
  · intro y
    apply Subtype.ext
    change lowerCapClamp ⟨H.toHomotopy (0, y), havoid (0, y)⟩ =
      lowerCapClamp ⟨(p.val y).1, sphLowerCap_coe_ne_sphNorthPole (p.val y)⟩
    have heq : (⟨H.toHomotopy (0, y), havoid (0, y)⟩ : SphNorthCompl d) =
        ⟨(p.val y).1, sphLowerCap_coe_ne_sphNorthPole (p.val y)⟩ :=
      Subtype.ext (H.map_zero_left y)
    rw [heq]
  · intro y
    apply Subtype.ext
    change lowerCapClamp ⟨H.toHomotopy (1, y), havoid (1, y)⟩ =
      lowerCapClamp ⟨(q.val y).1, sphLowerCap_coe_ne_sphNorthPole (q.val y)⟩
    have heq : (⟨H.toHomotopy (1, y), havoid (1, y)⟩ : SphNorthCompl d) =
        ⟨(q.val y).1, sphLowerCap_coe_ne_sphNorthPole (q.val y)⟩ :=
      Subtype.ext (H.map_one_left y)
    rw [heq]
  · intro u
    constructor
    · intro y hy
      exact (lowerCapClamp_mem_belt_of_mem_upperCap
        ((H.prop' u).1 y hy) (havoid (u, y))).2
    · intro y hy
      apply Subtype.ext
      change lowerCapClamp ⟨H.toHomotopy (u, y), havoid (u, y)⟩ =
        sphereBasepoint (d + 1)
      have hbase : H.toHomotopy (u, y) = sphereBasepoint (d + 1) :=
        (H.prop' u).2 y hy
      have heq : (⟨H.toHomotopy (u, y), havoid (u, y)⟩ : SphNorthCompl d) =
          ⟨sphereBasepoint (d + 1), sphereBasepoint_ne_sphNorthPole d⟩ :=
        Subtype.ext hbase
      rw [heq, lowerCapClamp_base]

/-- If a homotopy between two included source representatives can be chosen off the north pole,
then those source representatives were already relatively homotopic. -/
theorem relGenLoop_homotopic_of_map_homotopy_avoids_north
    {p q : RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d)}
    (H : ContinuousMap.HomotopyWith
      (RelGenLoop.map (sphCapInclusionPairMap d) p).val
      (RelGenLoop.map (sphCapInclusionPairMap d) q).val
      (fun f => f ∈ RelGenLoop n (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d)))
    (havoid : ∀ sy, H.toHomotopy sy ≠ sphNorthPole d) :
    RelGenLoop.Homotopic p q :=
  (capExcisionClampSourceRelGenLoop_homotopic p).trans <|
    (capExcisionClampSourceRelGenLoop_homotopic_of_targetHomotopy_avoids_north
      H havoid).trans (capExcisionClampSourceRelGenLoop_homotopic q).symm

/-- If every homotopy between included source representatives can be replaced by one avoiding
the north pole with the same endpoints, cap excision is injective. -/
theorem sphereSuspensionExcisionHomAt_injective_of_homotopies_avoiding_north
    (q : ℕ)
    (havoid : ∀ p r : RelGenLoop (q + 2) (sphLowerCap d)
        (sphCapOverlapInLower d) (sphCapOverlapBase d),
      RelGenLoop.Homotopic
          (RelGenLoop.map (sphCapInclusionPairMap d) p)
          (RelGenLoop.map (sphCapInclusionPairMap d) r) →
        ∃ H : ContinuousMap.HomotopyWith
            (RelGenLoop.map (sphCapInclusionPairMap d) p).val
            (RelGenLoop.map (sphCapInclusionPairMap d) r).val
            (fun f => f ∈ RelGenLoop (q + 2) (Sph (d + 1))
              (sphUpperCap d) (sphUpperCapBase d)),
          ∀ sy, H.toHomotopy sy ≠ sphNorthPole d) :
    Function.Injective (sphereSuspensionExcisionHomAt d q) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ p =>
      induction y using Quotient.inductionOn with
      | _ r =>
          change (⟦RelGenLoop.map (sphCapInclusionPairMap d) p⟧ :
              π_rel (q + 2) (Sph (d + 1)) (sphUpperCap d)
                (sphUpperCapBase d)) =
            ⟦RelGenLoop.map (sphCapInclusionPairMap d) r⟧ at hxy
          have hpr : RelGenLoop.Homotopic
              (RelGenLoop.map (sphCapInclusionPairMap d) p)
              (RelGenLoop.map (sphCapInclusionPairMap d) r) :=
            Quotient.exact hxy
          obtain ⟨H, hHavoid⟩ := havoid p r hpr
          exact Quotient.sound
            (relGenLoop_homotopic_of_map_homotopy_avoids_north H hHavoid)

/-- Representative avoidance for target maps and source homotopies is sufficient for full
bijectivity of the cap-excision map. -/
theorem sphereSuspensionExcisionHomAt_bijective_of_avoiding_north
    (q : ℕ)
    (hsurj : ∀ p : RelGenLoop (q + 2) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d),
      ∃ p' : RelGenLoop (q + 2) (Sph (d + 1))
          (sphUpperCap d) (sphUpperCapBase d),
        RelGenLoop.Homotopic p p' ∧ ∀ y, p'.val y ≠ sphNorthPole d)
    (hinj : ∀ p r : RelGenLoop (q + 2) (sphLowerCap d)
        (sphCapOverlapInLower d) (sphCapOverlapBase d),
      RelGenLoop.Homotopic
          (RelGenLoop.map (sphCapInclusionPairMap d) p)
          (RelGenLoop.map (sphCapInclusionPairMap d) r) →
        ∃ H : ContinuousMap.HomotopyWith
            (RelGenLoop.map (sphCapInclusionPairMap d) p).val
            (RelGenLoop.map (sphCapInclusionPairMap d) r).val
            (fun f => f ∈ RelGenLoop (q + 2) (Sph (d + 1))
              (sphUpperCap d) (sphUpperCapBase d)),
          ∀ sy, H.toHomotopy sy ≠ sphNorthPole d) :
    Function.Bijective (sphereSuspensionExcisionHomAt d q) :=
  ⟨sphereSuspensionExcisionHomAt_injective_of_homotopies_avoiding_north q hinj,
    sphereSuspensionExcisionHomAt_surjective_of_avoiding_north q hsurj⟩

end Submission
