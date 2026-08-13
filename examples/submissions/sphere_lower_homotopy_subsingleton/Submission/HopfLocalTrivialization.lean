/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.HopfMap

/-!
# Local product charts for the exact Hopf map

The explicit Hopf map is locally a product with the exact metric circle.  This file constructs
the two classical charts over the open sets `x₀ > -1` and `x₀ < 1`.  These are the geometric
input for proving that the map has the homotopy lifting property.
-/

open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

/-! ## The two base charts -/

/-- The northern Hopf chart consists of points away from the south pole. -/
def hopfNorthChart : Set (Sph 2) :=
  {y | -1 < (y : EuclideanSpace ℝ (Fin 3)) 0}

/-- The southern Hopf chart consists of points away from the north pole. -/
def hopfSouthChart : Set (Sph 2) :=
  {y | (y : EuclideanSpace ℝ (Fin 3)) 0 < 1}

theorem isOpen_hopfNorthChart : IsOpen hopfNorthChart := by
  apply isOpen_lt continuous_const
  exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp continuous_subtype_val

theorem isOpen_hopfSouthChart : IsOpen hopfSouthChart := by
  apply isOpen_lt
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp continuous_subtype_val
  · exact continuous_const

/-- The northern and southern charts cover the whole base sphere. -/
theorem hopfNorthChart_union_hopfSouthChart :
    hopfNorthChart ∪ hopfSouthChart = Set.univ := by
  ext y
  simp only [hopfNorthChart, hopfSouthChart, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ,
    iff_true]
  by_cases h : (y : EuclideanSpace ℝ (Fin 3)) 0 < 1
  · exact Or.inr h
  · exact Or.inl (by linarith)

abbrev HopfNorthBase := hopfNorthChart
abbrev HopfSouthBase := hopfSouthChart

/-! ## Northern section -/

/-- The positive first real coordinate of the standard northern local section. -/
noncomputable def hopfNorthRadius (y : HopfNorthBase) : ℝ :=
  √((1 + ((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) 0) / 2)

theorem hopfNorthRadius_pos (y : HopfNorthBase) : 0 < hopfNorthRadius y := by
  have hy := y.property
  change -1 < ((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) 0 at hy
  apply Real.sqrt_pos.2
  exact div_pos (by linarith) (by norm_num)

theorem hopfNorthRadius_ne_zero (y : HopfNorthBase) : hopfNorthRadius y ≠ 0 :=
  (hopfNorthRadius_pos y).ne'

theorem hopfNorthRadius_sq (y : HopfNorthBase) :
    hopfNorthRadius y ^ 2 =
      (1 + ((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) 0) / 2 := by
  have hy := y.property
  change -1 < ((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) 0 at hy
  exact Real.sq_sqrt (le_of_lt <| div_pos (by linarith) (by norm_num))

/-- The three coordinate squares of a point of `S^2` sum to one. -/
theorem sphereTwo_sum_sq (y : Sph 2) :
    (y : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 +
        (y : EuclideanSpace ℝ (Fin 3)) 1 ^ 2 +
        (y : EuclideanSpace ℝ (Fin 3)) 2 ^ 2 = 1 := by
  have h := congrArg (fun a : ℝ => a ^ 2) (norm_coe_sph y)
  rw [EuclideanSpace.real_norm_sq_eq] at h
  simpa [Fin.sum_univ_succ, add_assoc] using h

/-- Ambient coordinate formula for the northern local section of the Hopf map. -/
noncomputable def hopfNorthSectionVec (y : HopfNorthBase) :
    EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![
    hopfNorthRadius y,
    0,
    (((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) 1) / (2 * hopfNorthRadius y),
    -(((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) 2) / (2 * hopfNorthRadius y)]

@[simp] theorem hopfNorthSectionVec_zero (y : HopfNorthBase) :
    hopfNorthSectionVec y 0 = hopfNorthRadius y := by simp [hopfNorthSectionVec]

@[simp] theorem hopfNorthSectionVec_one (y : HopfNorthBase) :
    hopfNorthSectionVec y 1 = 0 := by simp [hopfNorthSectionVec]

@[simp] theorem hopfNorthSectionVec_two (y : HopfNorthBase) :
    hopfNorthSectionVec y 2 =
      ((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) 1 / (2 * hopfNorthRadius y) := by
  simp [hopfNorthSectionVec]

@[simp] theorem hopfNorthSectionVec_three (y : HopfNorthBase) :
    hopfNorthSectionVec y 3 =
      -((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) 2 / (2 * hopfNorthRadius y) := by
  simp [hopfNorthSectionVec]

/-- The northern section formula has unit norm. -/
theorem norm_hopfNorthSectionVec (y : HopfNorthBase) : ‖hopfNorthSectionVec y‖ = 1 := by
  apply norm_eq_one_of_norm_sq_eq_one
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [hopfNorthSectionVec, Fin.sum_univ_succ]
  have hs := sphereTwo_sum_sq (y : Sph 2)
  have hr := hopfNorthRadius_sq y
  have hr0 := hopfNorthRadius_ne_zero y
  field_simp
  nlinarith

/-- The northern section as a map into the exact metric `S^3`. -/
noncomputable def hopfNorthSection (y : HopfNorthBase) : Sph 3 :=
  ⟨hopfNorthSectionVec y, mem_sphere_zero_iff_norm.mpr (norm_hopfNorthSectionVec y)⟩

/-- The northern formula is a section of the Hopf map. -/
theorem hopfMap_hopfNorthSection (y : HopfNorthBase) :
    hopfMap (hopfNorthSection y) = (y : Sph 2) := by
  have hr := hopfNorthRadius_sq y
  have hr0 := hopfNorthRadius_ne_zero y
  have hs := sphereTwo_sum_sq (y : Sph 2)
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [hopfMap, hopfVec, hopfNorthSection]
    field_simp
    nlinarith
  · simp [hopfMap, hopfVec, hopfNorthSection]
    field_simp [hr0]
  · simp [hopfMap, hopfVec, hopfNorthSection]
    field_simp [hr0]

/-- The northern radius varies continuously. -/
theorem continuous_hopfNorthRadius : Continuous hopfNorthRadius := by
  have hc : Continuous fun y : HopfNorthBase =>
      ((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) 0 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  exact ((continuous_const.add hc).div_const 2).sqrt

/-- The ambient northern section formula varies continuously. -/
theorem continuous_hopfNorthSectionVec : Continuous hopfNorthSectionVec := by
  have hval : Continuous fun y : HopfNorthBase =>
      ((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hc (i : Fin 3) : Continuous fun y : HopfNorthBase =>
      ((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) i :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp hval
  have hden : Continuous fun y : HopfNorthBase => 2 * hopfNorthRadius y :=
    continuous_const.mul continuous_hopfNorthRadius
  have hden0 (y : HopfNorthBase) : 2 * hopfNorthRadius y ≠ 0 :=
    mul_ne_zero (by norm_num) (hopfNorthRadius_ne_zero y)
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp (continuous_pi fun i => ?_)
  fin_cases i
  · simpa [hopfNorthSectionVec] using continuous_hopfNorthRadius
  · simpa [hopfNorthSectionVec] using (continuous_const : Continuous fun _ : HopfNorthBase => (0 : ℝ))
  · change Continuous fun y : HopfNorthBase =>
      ((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) 1 / (2 * hopfNorthRadius y)
    exact (hc 1).div hden hden0
  · change Continuous fun y : HopfNorthBase =>
      -((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) 2 / (2 * hopfNorthRadius y)
    exact (hc 2).neg.div hden hden0

/-- The northern local section is continuous. -/
theorem continuous_hopfNorthSection : Continuous hopfNorthSection := by
  refine Continuous.subtype_mk continuous_hopfNorthSectionVec ?_

/-! ## The circle action -/

/-- Simultaneous complex multiplication on the two coordinate pairs of `R^4`. -/
noncomputable def hopfCircleActionVec
    (t : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![
    t 0 * x 0 - t 1 * x 1,
    t 1 * x 0 + t 0 * x 1,
    t 0 * x 2 - t 1 * x 3,
    t 1 * x 2 + t 0 * x 3]

@[simp] theorem hopfCircleActionVec_zero
    (t : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 4)) :
    hopfCircleActionVec t x 0 = t 0 * x 0 - t 1 * x 1 := by
  simp [hopfCircleActionVec]

@[simp] theorem hopfCircleActionVec_one
    (t : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 4)) :
    hopfCircleActionVec t x 1 = t 1 * x 0 + t 0 * x 1 := by
  simp [hopfCircleActionVec]

@[simp] theorem hopfCircleActionVec_two
    (t : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 4)) :
    hopfCircleActionVec t x 2 = t 0 * x 2 - t 1 * x 3 := by
  simp [hopfCircleActionVec]

@[simp] theorem hopfCircleActionVec_three
    (t : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 4)) :
    hopfCircleActionVec t x 3 = t 1 * x 2 + t 0 * x 3 := by
  simp [hopfCircleActionVec]

/-- Simultaneous complex multiplication multiplies squared norms. -/
theorem norm_hopfCircleActionVec_sq
    (t : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 4)) :
    ‖hopfCircleActionVec t x‖ ^ 2 = ‖t‖ ^ 2 * ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp [hopfCircleActionVec, Fin.sum_univ_succ]
  ring

/-- The ambient circle action is jointly continuous. -/
theorem continuous_hopfCircleActionVec :
    Continuous fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 4) =>
      hopfCircleActionVec p.1 p.2 := by
  unfold hopfCircleActionVec
  fun_prop

/-- The exact metric circle acts on the exact metric `3`-sphere. -/
noncomputable def hopfCircleAction (t : Sph 1) (x : Sph 3) : Sph 3 :=
  ⟨hopfCircleActionVec t x, mem_sphere_zero_iff_norm.mpr <| by
    apply norm_eq_one_of_norm_sq_eq_one
    rw [norm_hopfCircleActionVec_sq, norm_coe_sph, norm_coe_sph]
    norm_num⟩

/-- The Hopf circle action is jointly continuous. -/
theorem continuous_hopfCircleAction :
    Continuous fun p : Sph 1 × Sph 3 => hopfCircleAction p.1 p.2 := by
  have hval : Continuous fun p : Sph 1 × Sph 3 =>
      ((p.1 : EuclideanSpace ℝ (Fin 2)), (p.2 : EuclideanSpace ℝ (Fin 4))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  refine Continuous.subtype_mk (continuous_hopfCircleActionVec.comp hval) ?_

/-- The circle action preserves the Hopf map. -/
theorem hopfMap_hopfCircleAction (t : Sph 1) (x : Sph 3) :
    hopfMap (hopfCircleAction t x) = hopfMap x := by
  have ht := congrArg (fun a : ℝ => a ^ 2) (norm_coe_sph t)
  rw [EuclideanSpace.real_norm_sq_eq] at ht
  have ht' : (t : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 +
      (t : EuclideanSpace ℝ (Fin 2)) 1 ^ 2 = 1 := by
    simpa [Fin.sum_univ_succ] using ht
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [hopfMap, hopfVec, hopfCircleAction]
    ring_nf
    nlinarith
  · simp [hopfMap, hopfVec, hopfCircleAction]
    linear_combination
      (((x : EuclideanSpace ℝ (Fin 4)) 0 * (x : EuclideanSpace ℝ (Fin 4)) 2 +
        (x : EuclideanSpace ℝ (Fin 4)) 1 * (x : EuclideanSpace ℝ (Fin 4)) 3)) * ht'
  · simp [hopfMap, hopfVec, hopfCircleAction]
    linear_combination
      (((x : EuclideanSpace ℝ (Fin 4)) 1 * (x : EuclideanSpace ℝ (Fin 4)) 2 -
        (x : EuclideanSpace ℝ (Fin 4)) 0 * (x : EuclideanSpace ℝ (Fin 4)) 3)) * ht'

/-! ## Northern product trivialization -/

/-- The part of `S^3` lying over the northern base chart. -/
def hopfNorthTotalSet : Set (Sph 3) := hopfMap ⁻¹' hopfNorthChart

abbrev HopfNorthTotal := hopfNorthTotalSet

theorem isOpen_hopfNorthTotalSet : IsOpen hopfNorthTotalSet :=
  hopfMap.continuous.isOpen_preimage _ isOpen_hopfNorthChart

/-- The base coordinate of a point in the northern total-space chart. -/
noncomputable def hopfNorthBaseOfTotal (x : HopfNorthTotal) : HopfNorthBase :=
  ⟨hopfMap (x : Sph 3), x.property⟩

/-- The northern radius squared is the squared norm of the first complex coordinate. -/
theorem hopfNorthRadius_sq_of_total (x : HopfNorthTotal) :
    hopfNorthRadius (hopfNorthBaseOfTotal x) ^ 2 =
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 ^ 2 +
        ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 ^ 2 := by
  have hr := hopfNorthRadius_sq (hopfNorthBaseOfTotal x)
  have hs := sphereThree_sum_sq (x : Sph 3)
  change hopfNorthRadius (hopfNorthBaseOfTotal x) ^ 2 =
    (1 + (((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 ^ 2 +
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 ^ 2 -
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 2 ^ 2 -
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 3 ^ 2)) / 2 at hr
  nlinarith

/-- The circle phase of a point in the northern Hopf chart. -/
noncomputable def hopfNorthPhaseVec (x : HopfNorthTotal) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![
    ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 /
      hopfNorthRadius (hopfNorthBaseOfTotal x),
    ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 /
      hopfNorthRadius (hopfNorthBaseOfTotal x)]

@[simp] theorem hopfNorthPhaseVec_zero (x : HopfNorthTotal) :
    hopfNorthPhaseVec x 0 =
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 /
        hopfNorthRadius (hopfNorthBaseOfTotal x) := by
  simp [hopfNorthPhaseVec]

@[simp] theorem hopfNorthPhaseVec_one (x : HopfNorthTotal) :
    hopfNorthPhaseVec x 1 =
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 /
        hopfNorthRadius (hopfNorthBaseOfTotal x) := by
  simp [hopfNorthPhaseVec]

/-- The northern phase has unit norm. -/
theorem norm_hopfNorthPhaseVec (x : HopfNorthTotal) : ‖hopfNorthPhaseVec x‖ = 1 := by
  apply norm_eq_one_of_norm_sq_eq_one
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [hopfNorthPhaseVec, Fin.sum_univ_succ]
  have hr := hopfNorthRadius_sq_of_total x
  have hr0 := hopfNorthRadius_ne_zero (hopfNorthBaseOfTotal x)
  field_simp
  nlinarith

/-- The normalized northern circle phase. -/
noncomputable def hopfNorthPhase (x : HopfNorthTotal) : Sph 1 :=
  ⟨hopfNorthPhaseVec x, mem_sphere_zero_iff_norm.mpr (norm_hopfNorthPhaseVec x)⟩

/-- The northern base coordinate is continuous. -/
theorem continuous_hopfNorthBaseOfTotal : Continuous hopfNorthBaseOfTotal := by
  have h : Continuous fun x : HopfNorthTotal => hopfMap (x : Sph 3) :=
    hopfMap.continuous.comp continuous_subtype_val
  exact Continuous.subtype_mk h fun x => x.property

/-- The northern phase coordinate is continuous. -/
theorem continuous_hopfNorthPhaseVec : Continuous hopfNorthPhaseVec := by
  have hval : Continuous fun x : HopfNorthTotal =>
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hc (i : Fin 4) : Continuous fun x : HopfNorthTotal =>
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) i :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) i).comp hval
  have hr : Continuous fun x : HopfNorthTotal =>
      hopfNorthRadius (hopfNorthBaseOfTotal x) :=
    continuous_hopfNorthRadius.comp continuous_hopfNorthBaseOfTotal
  have hr0 (x : HopfNorthTotal) :
      hopfNorthRadius (hopfNorthBaseOfTotal x) ≠ 0 :=
    hopfNorthRadius_ne_zero _
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (continuous_pi fun i => ?_)
  fin_cases i
  · change Continuous fun x : HopfNorthTotal =>
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 /
        hopfNorthRadius (hopfNorthBaseOfTotal x)
    exact (hc 0).div hr hr0
  · change Continuous fun x : HopfNorthTotal =>
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 /
        hopfNorthRadius (hopfNorthBaseOfTotal x)
    exact (hc 1).div hr hr0

/-- The normalized northern phase coordinate is continuous. -/
theorem continuous_hopfNorthPhase : Continuous hopfNorthPhase := by
  refine Continuous.subtype_mk continuous_hopfNorthPhaseVec ?_

/-- Forward coordinates for the northern local product chart. -/
noncomputable def hopfNorthTrivializationTo (x : HopfNorthTotal) :
    HopfNorthBase × Sph 1 :=
  (hopfNorthBaseOfTotal x, hopfNorthPhase x)

/-- Inverse coordinates for the northern local product chart. -/
noncomputable def hopfNorthTrivializationFrom (p : HopfNorthBase × Sph 1) :
    HopfNorthTotal :=
  ⟨hopfCircleAction p.2 (hopfNorthSection p.1), by
    change hopfMap (hopfCircleAction p.2 (hopfNorthSection p.1)) ∈ hopfNorthChart
    rw [hopfMap_hopfCircleAction, hopfMap_hopfNorthSection]
    exact p.1.property⟩

theorem continuous_hopfNorthTrivializationTo : Continuous hopfNorthTrivializationTo :=
  continuous_hopfNorthBaseOfTotal.prodMk continuous_hopfNorthPhase

theorem continuous_hopfNorthTrivializationFrom : Continuous hopfNorthTrivializationFrom := by
  have h : Continuous fun p : HopfNorthBase × Sph 1 =>
      hopfCircleAction p.2 (hopfNorthSection p.1) :=
    continuous_hopfCircleAction.comp
      (continuous_snd.prodMk (continuous_hopfNorthSection.comp continuous_fst))
  exact Continuous.subtype_mk h fun p => by
    change hopfMap (hopfCircleAction p.2 (hopfNorthSection p.1)) ∈ hopfNorthChart
    rw [hopfMap_hopfCircleAction, hopfMap_hopfNorthSection]
    exact p.1.property

/-- Reconstructing a northern-chart point from its base and phase returns the point. -/
theorem hopfNorthTrivializationFrom_to (x : HopfNorthTotal) :
    hopfNorthTrivializationFrom (hopfNorthTrivializationTo x) = x := by
  let r := hopfNorthRadius (hopfNorthBaseOfTotal x)
  have hr : r ^ 2 =
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 ^ 2 +
        ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 ^ 2 :=
    hopfNorthRadius_sq_of_total x
  have hr0 : r ≠ 0 := hopfNorthRadius_ne_zero _
  apply Subtype.ext
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · change ((((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 / r) * r -
      (((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 / r) * 0) =
        ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0
    field_simp [hr0]
    ring
  · change ((((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 / r) * r +
      (((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 / r) * 0) =
        ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1
    field_simp [hr0]
    ring
  · change ((((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 / r) *
        (2 * (((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 *
          ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 2 +
          ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 *
          ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 3) / (2 * r)) -
      (((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 / r) *
        (- (2 * (((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 *
          ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 2 -
          ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 *
          ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 3)) / (2 * r))) =
        ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 2
    field_simp [hr0]
    rw [hr]
    ring
  · change ((((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 / r) *
        (2 * (((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 *
          ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 2 +
          ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 *
          ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 3) / (2 * r)) +
      (((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 / r) *
        (- (2 * (((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 *
          ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 2 -
          ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 *
          ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 3)) / (2 * r))) =
        ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 3
    field_simp [hr0]
    rw [hr]
    ring

/-- Taking northern coordinates after reconstruction returns the input coordinates. -/
theorem hopfNorthTrivializationTo_from (p : HopfNorthBase × Sph 1) :
    hopfNorthTrivializationTo (hopfNorthTrivializationFrom p) = p := by
  have hbase : hopfNorthBaseOfTotal (hopfNorthTrivializationFrom p) = p.1 := by
    apply Subtype.ext
    change hopfMap (hopfCircleAction p.2 (hopfNorthSection p.1)) = (p.1 : Sph 2)
    rw [hopfMap_hopfCircleAction, hopfMap_hopfNorthSection]
  apply Prod.ext
  · exact hbase
  · change hopfNorthPhase (hopfNorthTrivializationFrom p) = p.2
    apply Subtype.ext
    apply PiLp.ext
    intro i
    change hopfNorthPhaseVec (hopfNorthTrivializationFrom p) i =
      (p.2 : EuclideanSpace ℝ (Fin 2)) i
    unfold hopfNorthPhaseVec
    rw [hbase]
    have hr0 := hopfNorthRadius_ne_zero p.1
    fin_cases i
    · simp [hopfNorthTrivializationFrom, hopfCircleAction, hopfNorthSection]
      field_simp [hr0]
    · simp [hopfNorthTrivializationFrom, hopfCircleAction, hopfNorthSection]
      field_simp [hr0]

/-- The explicit northern product chart for the exact Hopf map. -/
noncomputable def hopfNorthTrivialization :
    HopfNorthTotal ≃ₜ HopfNorthBase × Sph 1 where
  toFun := hopfNorthTrivializationTo
  invFun := hopfNorthTrivializationFrom
  left_inv := hopfNorthTrivializationFrom_to
  right_inv := hopfNorthTrivializationTo_from
  continuous_toFun := continuous_hopfNorthTrivializationTo
  continuous_invFun := continuous_hopfNorthTrivializationFrom

/-- The first coordinate of the northern trivialization is the Hopf-map value. -/
@[simp]
theorem hopfNorthTrivialization_fst (x : HopfNorthTotal) :
    ((hopfNorthTrivialization x).1 : Sph 2) = hopfMap (x : Sph 3) :=
  rfl

/-! ## Symmetries and the southern product trivialization -/

/-- Swap the two complex coordinate pairs in the ambient `R^4`. -/
noncomputable def hopfSwapVec (x : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![x 2, x 3, x 0, x 1]

/-- Swapping the complex coordinate pairs preserves the norm. -/
theorem norm_hopfSwapVec (x : EuclideanSpace ℝ (Fin 4)) : ‖hopfSwapVec x‖ = ‖x‖ := by
  apply eq_of_sq_eq_sq_of_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [hopfSwapVec, Fin.sum_univ_succ]
  ring

theorem continuous_hopfSwapVec : Continuous hopfSwapVec := by
  unfold hopfSwapVec
  fun_prop

/-- Swapping the two complex coordinates as a self-homeomorphism of `S^3`. -/
noncomputable def hopfSwapHomeomorph : Sph 3 ≃ₜ Sph 3 where
  toFun x := ⟨hopfSwapVec x, mem_sphere_zero_iff_norm.mpr <| by
    rw [norm_hopfSwapVec, norm_coe_sph]⟩
  invFun x := ⟨hopfSwapVec x, mem_sphere_zero_iff_norm.mpr <| by
    rw [norm_hopfSwapVec, norm_coe_sph]⟩
  left_inv x := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hopfSwapVec]
  right_inv x := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hopfSwapVec]
  continuous_toFun := Continuous.subtype_mk
    (continuous_hopfSwapVec.comp continuous_subtype_val) fun x => by
      apply mem_sphere_zero_iff_norm.mpr
      change ‖hopfSwapVec (x : EuclideanSpace ℝ (Fin 4))‖ = 1
      rw [norm_hopfSwapVec, norm_coe_sph]
  continuous_invFun := Continuous.subtype_mk
    (continuous_hopfSwapVec.comp continuous_subtype_val) fun x => by
      apply mem_sphere_zero_iff_norm.mpr
      change ‖hopfSwapVec (x : EuclideanSpace ℝ (Fin 4))‖ = 1
      rw [norm_hopfSwapVec, norm_coe_sph]

/-- Reflect the first and third coordinates in the ambient `R^3`. -/
noncomputable def hopfBaseFlipVec (y : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![-y 0, y 1, -y 2]

theorem norm_hopfBaseFlipVec (y : EuclideanSpace ℝ (Fin 3)) :
    ‖hopfBaseFlipVec y‖ = ‖y‖ := by
  apply eq_of_sq_eq_sq_of_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [hopfBaseFlipVec, Fin.sum_univ_succ]

theorem continuous_hopfBaseFlipVec : Continuous hopfBaseFlipVec := by
  unfold hopfBaseFlipVec
  fun_prop

/-- The corresponding self-homeomorphism of the exact metric `S^2`. -/
noncomputable def hopfBaseFlipHomeomorph : Sph 2 ≃ₜ Sph 2 where
  toFun y := ⟨hopfBaseFlipVec y, mem_sphere_zero_iff_norm.mpr <| by
    rw [norm_hopfBaseFlipVec, norm_coe_sph]⟩
  invFun y := ⟨hopfBaseFlipVec y, mem_sphere_zero_iff_norm.mpr <| by
    rw [norm_hopfBaseFlipVec, norm_coe_sph]⟩
  left_inv y := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hopfBaseFlipVec]
  right_inv y := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hopfBaseFlipVec]
  continuous_toFun := Continuous.subtype_mk
    (continuous_hopfBaseFlipVec.comp continuous_subtype_val) fun y => by
      apply mem_sphere_zero_iff_norm.mpr
      change ‖hopfBaseFlipVec (y : EuclideanSpace ℝ (Fin 3))‖ = 1
      rw [norm_hopfBaseFlipVec, norm_coe_sph]
  continuous_invFun := Continuous.subtype_mk
    (continuous_hopfBaseFlipVec.comp continuous_subtype_val) fun y => by
      apply mem_sphere_zero_iff_norm.mpr
      change ‖hopfBaseFlipVec (y : EuclideanSpace ℝ (Fin 3))‖ = 1
      rw [norm_hopfBaseFlipVec, norm_coe_sph]

/-- Swapping the two complex coordinates covers the indicated reflection of `S^2`. -/
theorem hopfMap_hopfSwapHomeomorph (x : Sph 3) :
    hopfMap (hopfSwapHomeomorph x) = hopfBaseFlipHomeomorph (hopfMap x) := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [hopfMap, hopfVec, hopfSwapHomeomorph, hopfSwapVec,
      hopfBaseFlipHomeomorph, hopfBaseFlipVec] <;> ring

/-- Reflection identifies the southern base chart with the northern one. -/
noncomputable def hopfSouthToNorthBaseHomeomorph : HopfSouthBase ≃ₜ HopfNorthBase :=
  Homeomorph.subtype hopfBaseFlipHomeomorph fun y => by
    change ((y : Sph 2) : EuclideanSpace ℝ (Fin 3)) 0 < 1 ↔
      -1 < (hopfBaseFlipHomeomorph (y : Sph 2) : EuclideanSpace ℝ (Fin 3)) 0
    simp [hopfBaseFlipHomeomorph, hopfBaseFlipVec]

/-- The part of `S^3` lying over the southern base chart. -/
def hopfSouthTotalSet : Set (Sph 3) := hopfMap ⁻¹' hopfSouthChart

abbrev HopfSouthTotal := hopfSouthTotalSet

theorem isOpen_hopfSouthTotalSet : IsOpen hopfSouthTotalSet :=
  hopfMap.continuous.isOpen_preimage _ isOpen_hopfSouthChart

/-- Swapping complex coordinates identifies the southern total-space chart with the northern
one. -/
noncomputable def hopfSouthToNorthTotalHomeomorph : HopfSouthTotal ≃ₜ HopfNorthTotal :=
  Homeomorph.subtype hopfSwapHomeomorph fun x => by
    change hopfMap (x : Sph 3) ∈ hopfSouthChart ↔
      hopfMap (hopfSwapHomeomorph (x : Sph 3)) ∈ hopfNorthChart
    rw [hopfMap_hopfSwapHomeomorph]
    change ((hopfMap (x : Sph 3) : Sph 2) : EuclideanSpace ℝ (Fin 3)) 0 < 1 ↔
      -1 < (hopfBaseFlipHomeomorph (hopfMap (x : Sph 3)) :
        EuclideanSpace ℝ (Fin 3)) 0
    simp [hopfBaseFlipHomeomorph, hopfBaseFlipVec]

/-- The explicit southern product chart, obtained from the northern chart by symmetry. -/
noncomputable def hopfSouthTrivialization :
    HopfSouthTotal ≃ₜ HopfSouthBase × Sph 1 :=
  hopfSouthToNorthTotalHomeomorph.trans <|
    hopfNorthTrivialization.trans <|
      Homeomorph.prodCongr hopfSouthToNorthBaseHomeomorph.symm (Homeomorph.refl _)

/-- The first coordinate of the southern trivialization is the Hopf-map value. -/
@[simp]
theorem hopfSouthTrivialization_fst (x : HopfSouthTotal) :
    ((hopfSouthTrivialization x).1 : Sph 2) = hopfMap (x : Sph 3) := by
  change hopfBaseFlipHomeomorph
      ((hopfNorthTrivialization (hopfSouthToNorthTotalHomeomorph x)).1 : Sph 2) =
    hopfMap (x : Sph 3)
  rw [hopfNorthTrivialization_fst]
  change hopfBaseFlipHomeomorph (hopfMap (hopfSwapHomeomorph (x : Sph 3))) =
    hopfMap (x : Sph 3)
  rw [hopfMap_hopfSwapHomeomorph]
  exact hopfBaseFlipHomeomorph.left_inv (hopfMap (x : Sph 3))

/-- A circle local trivialization of a continuous map at a point of its base. -/
def HasCircleLocalTrivializationAt {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) : Prop :=
  ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
    ∃ e : (p ⁻¹' U : Set E) ≃ₜ U × Sph 1,
      ∀ x, ((e x).1 : B) = p (x : E)

/-- The two explicit product charts prove local triviality of the exact Hopf map at every point
of `S^2`. -/
theorem hopfMap_hasCircleLocalTrivializationAt (y : Sph 2) :
    HasCircleLocalTrivializationAt hopfMap y := by
  have hcover : y ∈ hopfNorthChart ∪ hopfSouthChart := by
    rw [hopfNorthChart_union_hopfSouthChart]
    exact Set.mem_univ y
  rcases hcover with hn | hs
  · exact ⟨hopfNorthChart, isOpen_hopfNorthChart, hn,
      hopfNorthTrivialization, hopfNorthTrivialization_fst⟩
  · exact ⟨hopfSouthChart, isOpen_hopfSouthChart, hs,
      hopfSouthTrivialization, hopfSouthTrivialization_fst⟩

end Submission
