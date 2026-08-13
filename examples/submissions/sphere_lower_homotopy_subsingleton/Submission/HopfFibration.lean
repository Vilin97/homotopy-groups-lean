/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.HopfTransport

/-!
# The exact Hopf map is a Serre fibration

Short non-antipodal transport lifts a homotopy whose image varies by less than one on a time
interval.  Uniform continuity supplies a dyadic scale on every compact cube.  Recursively
lifting the lower and upper halves and pasting them at equal speed produces a lift with the
original time parametrization.
-/

open unitInterval
open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

/-! ## Dyadic reparametrizations -/

/-- Reparametrize the unit interval onto its lower half. -/
def hopfLowerHalfTime (t : I) : I :=
  ⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.2.1, t.2.2]⟩

/-- Reparametrize the unit interval onto its upper half. -/
def hopfUpperHalfTime (t : I) : I :=
  ⟨((t : ℝ) + 1) / 2, by constructor <;> nlinarith [t.2.1, t.2.2]⟩

@[simp] theorem coe_hopfLowerHalfTime (t : I) :
    (hopfLowerHalfTime t : ℝ) = (t : ℝ) / 2 := rfl

@[simp] theorem coe_hopfUpperHalfTime (t : I) :
    (hopfUpperHalfTime t : ℝ) = ((t : ℝ) + 1) / 2 := rfl

theorem continuous_hopfLowerHalfTime : Continuous hopfLowerHalfTime := by
  unfold hopfLowerHalfTime
  fun_prop

theorem continuous_hopfUpperHalfTime : Continuous hopfUpperHalfTime := by
  unfold hopfUpperHalfTime
  fun_prop

@[simp] theorem hopfLowerHalfTime_zero : hopfLowerHalfTime 0 = 0 := by
  ext
  norm_num

@[simp] theorem hopfUpperHalfTime_one : hopfUpperHalfTime 1 = 1 := by
  ext
  norm_num

theorem hopfLowerHalfTime_one_eq_hopfUpperHalfTime_zero :
    hopfLowerHalfTime 1 = hopfUpperHalfTime 0 := by
  ext
  norm_num

theorem dist_hopfLowerHalfTime (s t : I) :
    dist (hopfLowerHalfTime s) (hopfLowerHalfTime t) = dist s t / 2 := by
  change |(s : ℝ) / 2 - (t : ℝ) / 2| = |(s : ℝ) - (t : ℝ)| / 2
  have h : (s : ℝ) / 2 - (t : ℝ) / 2 = ((s : ℝ) - (t : ℝ)) / 2 := by ring
  rw [h, abs_div]
  norm_num

theorem dist_hopfUpperHalfTime (s t : I) :
    dist (hopfUpperHalfTime s) (hopfUpperHalfTime t) = dist s t / 2 := by
  change |((s : ℝ) + 1) / 2 - ((t : ℝ) + 1) / 2| =
    |(s : ℝ) - (t : ℝ)| / 2
  have h : ((s : ℝ) + 1) / 2 - ((t : ℝ) + 1) / 2 =
      ((s : ℝ) - (t : ℝ)) / 2 := by ring
  rw [h, abs_div]
  norm_num

theorem unitInterval_dist_le_one (s t : I) : dist s t ≤ 1 := by
  change |(s : ℝ) - (t : ℝ)| ≤ 1
  rw [abs_le]
  constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]

/-- Reparametrize a cylinder onto its lower time half. -/
def hopfLowerHalfCylinder (A : Type*) [TopologicalSpace A] : C(I × A, I × A) where
  toFun z := (hopfLowerHalfTime z.1, z.2)
  continuous_toFun := continuous_hopfLowerHalfTime.comp continuous_fst |>.prodMk continuous_snd

/-- Reparametrize a cylinder onto its upper time half. -/
def hopfUpperHalfCylinder (A : Type*) [TopologicalSpace A] : C(I × A, I × A) where
  toFun z := (hopfUpperHalfTime z.1, z.2)
  continuous_toFun := continuous_hopfUpperHalfTime.comp continuous_fst |>.prodMk continuous_snd

/-- Restrict a homotopy-shaped continuous map to the lower half of its time interval. -/
def hopfLowerHalf {A Y : Type*} [TopologicalSpace A] [TopologicalSpace Y]
    (H : C(I × A, Y)) : C(I × A, Y) :=
  H.comp (hopfLowerHalfCylinder A)

/-- Restrict a homotopy-shaped continuous map to the upper half of its time interval. -/
def hopfUpperHalf {A Y : Type*} [TopologicalSpace A] [TopologicalSpace Y]
    (H : C(I × A, Y)) : C(I × A, Y) :=
  H.comp (hopfUpperHalfCylinder A)

@[simp] theorem hopfLowerHalf_apply {A Y : Type*} [TopologicalSpace A] [TopologicalSpace Y]
    (H : C(I × A, Y)) (z : I × A) :
    hopfLowerHalf H z = H (hopfLowerHalfTime z.1, z.2) := rfl

@[simp] theorem hopfUpperHalf_apply {A Y : Type*} [TopologicalSpace A] [TopologicalSpace Y]
    (H : C(I × A, Y)) (z : I × A) :
    hopfUpperHalf H z = H (hopfUpperHalfTime z.1, z.2) := rfl

/-! ## Controlled short lifts -/

/-- On time intervals of dyadic length `2^-m`, the base homotopy moves by less than one. -/
def HopfDyadicControl {A : Type*} [TopologicalSpace A]
    (m : ℕ) (H : C(I × A, Sph 2)) : Prop :=
  ∀ s t a, dist s t ≤ (1 / 2 : ℝ) ^ m → dist (H (s, a)) (H (t, a)) < 1

/-- Dyadic control restricts to the lower half, with the exponent decreased by one. -/
theorem HopfDyadicControl.lowerHalf
    {A : Type*} [TopologicalSpace A] {m : ℕ} {H : C(I × A, Sph 2)}
    (h : HopfDyadicControl (m + 1) H) :
    HopfDyadicControl m (hopfLowerHalf H) := by
  intro s t a hst
  apply h (hopfLowerHalfTime s) (hopfLowerHalfTime t) a
  rw [dist_hopfLowerHalfTime, pow_succ]
  nlinarith

/-- Dyadic control restricts to the upper half, with the exponent decreased by one. -/
theorem HopfDyadicControl.upperHalf
    {A : Type*} [TopologicalSpace A] {m : ℕ} {H : C(I × A, Sph 2)}
    (h : HopfDyadicControl (m + 1) H) :
    HopfDyadicControl m (hopfUpperHalf H) := by
  intro s t a hst
  apply h (hopfUpperHalfTime s) (hopfUpperHalfTime t) a
  rw [dist_hopfUpperHalfTime, pow_succ]
  nlinarith

/-- A homotopy controlled at scale one has a lift by direct non-antipodal transport from its
initial stage. -/
theorem exists_hopfLift_of_dyadicControl_zero
    {A : Type*} [TopologicalSpace A]
    (f : C(A, Sph 3)) (H : C(I × A, Sph 2))
    (hzero : ∀ a, H (0, a) = hopfMap (f a))
    (hcontrol : HopfDyadicControl 0 H) :
    ∃ L : C(I × A, Sph 3),
      (∀ a, L (0, a) = f a) ∧ ∀ z, hopfMap (L z) = H z := by
  let D : C(I × A, HopfTransportDomain) :=
    { toFun := fun z => ⟨(f z.2, H z), by
        apply neg_one_lt_hopfBaseDot_of_dist_lt_two
        calc
          dist (H z) (hopfMap (f z.2)) = dist (H z) (H (0, z.2)) := by rw [hzero]
          _ < 1 := hcontrol z.1 0 z.2 (by
            simp only [pow_zero]
            exact unitInterval_dist_le_one _ _)
          _ < 2 := by norm_num⟩
      continuous_toFun := by
        apply continuous_induced_rng.2
        exact (f.continuous.comp continuous_snd).prodMk H.continuous }
  refine ⟨⟨fun z => hopfTransport (D z),
      continuous_hopfTransport.comp D.continuous⟩, ?_, ?_⟩
  · intro a
    have hD : D (0, a) = hopfTransportSelf (f a) := by
      apply Subtype.ext
      exact Prod.ext rfl (hzero a)
    change hopfTransport (D (0, a)) = f a
    rw [hD, hopfTransport_self]
  · intro z
    exact hopfMap_hopfTransport (D z)

/-- A dyadically controlled homotopy has a lift.  The induction pastes equal lower and upper
time halves, so the resulting lift lies over the original parametrized homotopy. -/
theorem exists_hopfLift_of_dyadicControl
    {A : Type*} [TopologicalSpace A]
    (m : ℕ) (f : C(A, Sph 3)) (H : C(I × A, Sph 2))
    (hzero : ∀ a, H (0, a) = hopfMap (f a))
    (hcontrol : HopfDyadicControl m H) :
    ∃ L : C(I × A, Sph 3),
      (∀ a, L (0, a) = f a) ∧ ∀ z, hopfMap (L z) = H z := by
  induction m generalizing f H with
  | zero => exact exists_hopfLift_of_dyadicControl_zero f H hzero hcontrol
  | succ m ih =>
      have hzeroLower : ∀ a, hopfLowerHalf H (0, a) = hopfMap (f a) := by
        intro a
        simpa using hzero a
      obtain ⟨L, hLzero, hLproj⟩ :=
        ih f (hopfLowerHalf H) hzeroLower hcontrol.lowerHalf
      let fmid : C(A, Sph 3) :=
        { toFun := fun a => L (1, a)
          continuous_toFun := L.continuous.comp (continuous_const.prodMk continuous_id) }
      have hzeroUpper : ∀ a, hopfUpperHalf H (0, a) = hopfMap (fmid a) := by
        intro a
        calc
          hopfUpperHalf H (0, a) = hopfLowerHalf H (1, a) := by
            change H (hopfUpperHalfTime 0, a) = H (hopfLowerHalfTime 1, a)
            rw [hopfLowerHalfTime_one_eq_hopfUpperHalfTime_zero]
          _ = hopfMap (L (1, a)) := (hLproj (1, a)).symm
          _ = hopfMap (fmid a) := rfl
      obtain ⟨R, hRzero, hRproj⟩ :=
        ih fmid (hopfUpperHalf H) hzeroUpper hcontrol.upperHalf
      let fend : C(A, Sph 3) :=
        { toFun := fun a => R (1, a)
          continuous_toFun := R.continuous.comp (continuous_const.prodMk continuous_id) }
      let Lhom : ContinuousMap.Homotopy f fmid :=
        { toFun := L
          continuous_toFun := L.continuous
          map_zero_left := hLzero
          map_one_left := fun _ => rfl }
      let Rhom : ContinuousMap.Homotopy fmid fend :=
        { toFun := R
          continuous_toFun := R.continuous
          map_zero_left := hRzero
          map_one_left := fun _ => rfl }
      let K : ContinuousMap.Homotopy f fend := Lhom.trans Rhom
      refine ⟨K.toContinuousMap, K.map_zero_left, ?_⟩
      intro z
      dsimp [K]
      rw [ContinuousMap.Homotopy.trans_apply]
      split_ifs with hz
      · change hopfMap (L _) = H z
        rw [hLproj]
        apply ContinuousMap.congr_arg H
        apply Prod.ext
        · apply Subtype.ext
          change (2 * (z.1 : ℝ)) / 2 = (z.1 : ℝ)
          ring
        · rfl
      · change hopfMap (R _) = H z
        rw [hRproj]
        apply ContinuousMap.congr_arg H
        apply Prod.ext
        · apply Subtype.ext
          change ((2 * (z.1 : ℝ) - 1) + 1) / 2 = (z.1 : ℝ)
          ring
        · rfl

/-! ## Uniform control on cubes and the fibration theorem -/

/-- A continuous homotopy on a compact metric parameter space is controlled at some dyadic
time scale. -/
theorem exists_hopfDyadicControl
    {A : Type*} [PseudoMetricSpace A] [CompactSpace A]
    (H : C(I × A, Sph 2)) : ∃ m, HopfDyadicControl m H := by
  have huc : UniformContinuous H :=
    CompactSpace.uniformContinuous_of_continuous H.continuous
  obtain ⟨delta, hdelta, hmove⟩ :=
    Metric.uniformContinuous_iff.mp huc 1 (by norm_num)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (1 / 2 : ℝ) ^ m < delta :=
    exists_pow_lt_of_lt_one hdelta (by norm_num)
  refine ⟨m, ?_⟩
  intro s t a hst
  apply hmove
  rw [dist_prod_same_right]
  exact lt_of_le_of_lt hst hm

/-- The exact Hopf map has the homotopy lifting property with respect to every finite cube. -/
theorem hopfMap_hasHLP_cube (n : ℕ) :
    HasHLP hopfMap (Fin n → I) := by
  intro f H hzero
  obtain ⟨m, hcontrol⟩ := exists_hopfDyadicControl H
  exact exists_hopfLift_of_dyadicControl m f H hzero hcontrol

/-- The explicit Hopf map `S^3 -> S^2` is a Serre fibration. -/
theorem hopfMap_isSerreFibration : IsSerreFibration hopfMap :=
  hopfMap_hasHLP_cube

/-! ## The first off-diagonal homotopy group of spheres -/

/-- The third homotopy group of the exact metric `2`-sphere is infinite cyclic. -/
theorem pi3_sphere_two_mulEquiv_int :
    Nonempty
      (π_ 3 (Sph 2) (sphereBasepoint 2) ≃* Multiplicative ℤ) :=
  pi3_sphere_two_mulEquiv_int_of_hopf_isSerreFibration hopfMap_isSerreFibration

end Submission
