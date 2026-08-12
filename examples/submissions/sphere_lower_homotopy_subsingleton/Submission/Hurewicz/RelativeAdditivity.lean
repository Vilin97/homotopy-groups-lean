/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SmallRelativeChains
import Submission.Hurewicz.CubeFundamentalClass
import Submission.Hurewicz.SimplexCubeClass
import Submission.Homotopy.RelGroup

/-!
# Additivity of the relative Hurewicz comparison

Cubical concatenation is replaced by a homotopic concatenation which is constant throughout the
middle third of the concatenating coordinate.  A two-member small-simplices cover then makes the
chain identity local: on every subordinate simplex the plateau concatenation is either its left
summand, its right summand, or the constant map into the subspace.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.alternatingFaceMapComplex AlgebraicTopology.AlternatingFaceMapComplex.obj
  SSet.chainComplexFunctor AlgebraicTopology.singularChainComplexFunctor
  CategoryTheory.Functor.postcompose₂ CategoryTheory.SimplicialObject.whiskering
  CategoryTheory.Functor.whiskeringLeft CategoryTheory.Functor.comp

noncomputable section

namespace Submission

/-! ### A pause in the middle third -/

/-- The clamped reparametrisation `t ↦ 3t`. -/
def firstThird (t : I) : I :=
  Set.projIcc (0 : ℝ) 1 zero_le_one (3 * t)

/-- The clamped reparametrisation `t ↦ 3t - 2`. -/
def lastThird (t : I) : I :=
  Set.projIcc (0 : ℝ) 1 zero_le_one (3 * t - 2)

/-- Reparametrise the interval so that it pauses at `1/2` on the middle third.  Averaging the
two clamped third-reparametrisations gives the three formulas `3t/2`, `1/2`, and
`(3t-1)/2` without a piecewise continuity proof. -/
def middleThirdPause (t : I) : I :=
  ⟨((firstThird t : ℝ) + (lastThird t : ℝ)) / 2, by
    have h10 : 0 ≤ (firstThird t : ℝ) := (firstThird t).2.1
    have h11 : (firstThird t : ℝ) ≤ 1 := (firstThird t).2.2
    have h20 : 0 ≤ (lastThird t : ℝ) := (lastThird t).2.1
    have h21 : (lastThird t : ℝ) ≤ 1 := (lastThird t).2.2
    constructor <;> linarith⟩

@[fun_prop]
theorem continuous_firstThird : Continuous firstThird :=
  continuous_projIcc.comp' (by fun_prop)

@[fun_prop]
theorem continuous_lastThird : Continuous lastThird :=
  continuous_projIcc.comp' (by fun_prop)

@[fun_prop]
theorem continuous_middleThirdPause : Continuous middleThirdPause := by
  apply Continuous.subtype_mk
  fun_prop

@[simp]
theorem middleThirdPause_zero : middleThirdPause 0 = 0 := by
  apply Subtype.ext
  simp [middleThirdPause, firstThird, lastThird, Set.projIcc]

@[simp]
theorem middleThirdPause_one : middleThirdPause 1 = 1 := by
  apply Subtype.ext
  norm_num [middleThirdPause, firstThird, lastThird, Set.projIcc]

/-- Before the end of the middle third, the paused parameter has not passed `1/2`. -/
theorem middleThirdPause_le_half {t : I} (ht : (t : ℝ) ≤ 2 / 3) :
    (middleThirdPause t : ℝ) ≤ 1 / 2 := by
  have hlast : lastThird t = 0 := by
    apply Subtype.ext
    change ((Set.projIcc (0 : ℝ) 1 zero_le_one (3 * (t : ℝ) - 2) : I) : ℝ) = 0
    rw [Set.projIcc_of_le_left]
    linarith
  change ((firstThird t : ℝ) + (lastThird t : ℝ)) / 2 ≤ 1 / 2
  rw [hlast]
  have h := (firstThird t).2.2
  norm_num at h ⊢
  linarith

/-- After the start of the middle third, the paused parameter is at least `1/2`. -/
theorem half_le_middleThirdPause {t : I} (ht : 1 / 3 ≤ (t : ℝ)) :
    1 / 2 ≤ (middleThirdPause t : ℝ) := by
  have hfirst : firstThird t = 1 := by
    apply Subtype.ext
    change ((Set.projIcc (0 : ℝ) 1 zero_le_one (3 * (t : ℝ)) : I) : ℝ) = 1
    rw [Set.projIcc_of_right_le]
    linarith
  change 1 / 2 ≤ ((firstThird t : ℝ) + (lastThird t : ℝ)) / 2
  rw [hfirst]
  have h := (lastThird t).2.1
  norm_num at h ⊢
  linarith

/-- The source parameter used by the left loop in plateau concatenation. -/
def leftPlateauParam (t : I) : I :=
  _root_.RelGenLoop.firstHalf (middleThirdPause t)

/-- The source parameter used by the right loop in plateau concatenation. -/
def rightPlateauParam (t : I) : I :=
  _root_.RelGenLoop.secondHalf (middleThirdPause t)

@[fun_prop]
theorem continuous_leftPlateauParam : Continuous leftPlateauParam := by
  unfold leftPlateauParam
  fun_prop

@[fun_prop]
theorem continuous_rightPlateauParam : Continuous rightPlateauParam := by
  unfold rightPlateauParam
  fun_prop

@[simp]
theorem leftPlateauParam_zero : leftPlateauParam 0 = 0 := by
  simp [leftPlateauParam]

@[simp]
theorem leftPlateauParam_one : leftPlateauParam 1 = 1 := by
  apply Subtype.ext
  norm_num [leftPlateauParam, _root_.RelGenLoop.firstHalf, Set.projIcc]

@[simp]
theorem rightPlateauParam_zero : rightPlateauParam 0 = 0 := by
  apply Subtype.ext
  norm_num [rightPlateauParam, _root_.RelGenLoop.secondHalf, Set.projIcc]

@[simp]
theorem rightPlateauParam_one : rightPlateauParam 1 = 1 := by
  simp [rightPlateauParam]

/-- The left parameter is fixed at its endpoint throughout the overlap and right region. -/
theorem leftPlateauParam_eq_one {t : I} (ht : 1 / 3 ≤ (t : ℝ)) :
    leftPlateauParam t = 1 := by
  apply Subtype.ext
  change ((Set.projIcc (0 : ℝ) 1 zero_le_one
    (2 * (middleThirdPause t : ℝ)) : I) : ℝ) = 1
  rw [Set.projIcc_of_right_le]
  linarith [half_le_middleThirdPause ht]

/-- The right parameter is fixed at its initial endpoint throughout the left region and
overlap. -/
theorem rightPlateauParam_eq_zero {t : I} (ht : (t : ℝ) ≤ 2 / 3) :
    rightPlateauParam t = 0 := by
  apply Subtype.ext
  change ((Set.projIcc (0 : ℝ) 1 zero_le_one
    (2 * (middleThirdPause t : ℝ) - 1) : I) : ℝ) = 0
  rw [Set.projIcc_of_le_left]
  linarith [middleThirdPause_le_half ht]

/-- Linear interpolation from the identity reparametrisation to `middleThirdPause`. -/
def middleThirdPauseHomotopy (st : I × I) : I :=
  Set.Icc.convexComb st.2 (middleThirdPause st.2) st.1

@[fun_prop]
theorem continuous_middleThirdPauseHomotopy : Continuous middleThirdPauseHomotopy := by
  unfold middleThirdPauseHomotopy
  fun_prop

@[simp]
theorem middleThirdPauseHomotopy_zero (t : I) :
    middleThirdPauseHomotopy (0, t) = t :=
  Set.Icc.convexComb_zero _ _

@[simp]
theorem middleThirdPauseHomotopy_one (t : I) :
    middleThirdPauseHomotopy (1, t) = middleThirdPause t :=
  Set.Icc.convexComb_one _ _

@[simp]
theorem middleThirdPauseHomotopy_zero_coord (s : I) :
    middleThirdPauseHomotopy (s, 0) = 0 := by
  simp [middleThirdPauseHomotopy]

@[simp]
theorem middleThirdPauseHomotopy_one_coord (s : I) :
    middleThirdPauseHomotopy (s, 1) = 1 := by
  simp [middleThirdPauseHomotopy]

namespace RelGenLoop

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}

/-- Precompose a relative cubical loop with the middle-third pause in a free coordinate. -/
def pauseAt (i : Fin n) (p : RelGenLoop (n + 1) X A a) : RelGenLoop (n + 1) X A a :=
  ⟨p.val.comp ⟨fun y ↦ Function.update y i.castSucc (middleThirdPause (y i.castSucc)),
      Cube.continuous_update _ (by fun_prop)⟩,
    fun y hy ↦ p.property.1 _ (by
      change Function.update y i.castSucc (middleThirdPause (y i.castSucc)) ∈ ∂I^(n + 1)
      by_cases hyi : y i.castSucc = 0 ∨ y i.castSucc = 1
      · rcases hyi with hi | hi
        · rw [hi, middleThirdPause_zero, ← hi, Function.update_eq_self]
          exact hy
        · rw [hi, middleThirdPause_one, ← hi, Function.update_eq_self]
          exact hy
      · exact Cube.update_mem_boundary hy hyi _),
    fun y hy ↦ p.property.2 _ (by
      change Function.update y i.castSucc (middleThirdPause (y i.castSucc)) ∈ ⊔I^(n + 1)
      by_cases hyi : y i.castSucc = 0 ∨ y i.castSucc = 1
      · rcases hyi with hi | hi
        · rw [hi, middleThirdPause_zero, ← hi, Function.update_eq_self]
          exact hy
        · rw [hi, middleThirdPause_one, ← hi, Function.update_eq_self]
          exact hy
      · exact Cube.update_mem_boundaryJar (Fin.castSucc_ne_last i) hy hyi _)⟩

@[simp]
theorem pauseAt_apply (i : Fin n) (p : RelGenLoop (n + 1) X A a)
    (y : I^Fin (n + 1)) :
    (pauseAt i p).val y =
      p.val (Function.update y i.castSucc (middleThirdPause (y i.castSucc))) :=
  rfl

/-- Pausing a relative loop is a relative homotopy reparametrisation. -/
theorem homotopic_pauseAt (i : Fin n) (p : RelGenLoop (n + 1) X A a) :
    _root_.RelGenLoop.Homotopic p (pauseAt i p) := by
  refine ⟨{
    toFun := fun sy ↦ p.val (Function.update sy.2 i.castSucc
      (middleThirdPauseHomotopy (sy.1, sy.2 i.castSucc)))
    continuous_toFun := p.val.continuous.comp' (by
      apply continuous_pi
      intro k
      rcases eq_or_ne k i.castSucc with rfl | hk
      · simpa only [Function.update_self] using (by fun_prop :
          Continuous fun sy : I × (I^Fin (n + 1)) ↦
            middleThirdPauseHomotopy (sy.1, sy.2 i.castSucc))
      · simpa only [Function.update_of_ne hk] using (by fun_prop :
          Continuous fun sy : I × (I^Fin (n + 1)) ↦ sy.2 k))
    map_zero_left := fun y ↦ by simp
    map_one_left := fun y ↦ by rw [pauseAt_apply, middleThirdPauseHomotopy_one]
    prop' := fun s ↦ ⟨
      fun y hy ↦ p.property.1 _ (by
        change Function.update y i.castSucc
          (middleThirdPauseHomotopy (s, y i.castSucc)) ∈ ∂I^(n + 1)
        by_cases hyi : y i.castSucc = 0 ∨ y i.castSucc = 1
        · rcases hyi with hi | hi
          · rw [hi, middleThirdPauseHomotopy_zero_coord, ← hi,
              Function.update_eq_self]
            exact hy
          · rw [hi, middleThirdPauseHomotopy_one_coord, ← hi,
              Function.update_eq_self]
            exact hy
        · exact Cube.update_mem_boundary hy hyi _),
      fun y hy ↦ p.property.2 _ (by
        change Function.update y i.castSucc
          (middleThirdPauseHomotopy (s, y i.castSucc)) ∈ ⊔I^(n + 1)
        by_cases hyi : y i.castSucc = 0 ∨ y i.castSucc = 1
        · rcases hyi with hi | hi
          · rw [hi, middleThirdPauseHomotopy_zero_coord, ← hi,
              Function.update_eq_self]
            exact hy
          · rw [hi, middleThirdPauseHomotopy_one_coord, ← hi,
              Function.update_eq_self]
            exact hy
        · exact Cube.update_mem_boundaryJar (Fin.castSucc_ne_last i) hy hyi _)
      ⟩ }⟩

/-- Concatenation with a constant middle third. -/
def plateauTransAt (i : Fin n) (p q : RelGenLoop (n + 1) X A a) :
    RelGenLoop (n + 1) X A a :=
  pauseAt i (_root_.RelGenLoop.transAt i p q)

/-- Plateau concatenation is relatively homotopic to ordinary cubical concatenation. -/
theorem homotopic_plateauTransAt (i : Fin n) (p q : RelGenLoop (n + 1) X A a) :
    _root_.RelGenLoop.Homotopic (_root_.RelGenLoop.transAt i p q)
      (plateauTransAt i p q) :=
  homotopic_pauseAt i _

/-- Reparametrise one free coordinate by a continuous interval self-map fixing both endpoints. -/
def reparamAt (i : Fin n) (r : C(I, I)) (hzero : r 0 = 0) (hone : r 1 = 1)
    (p : RelGenLoop (n + 1) X A a) : RelGenLoop (n + 1) X A a :=
  ⟨p.val.comp ⟨fun y ↦ Function.update y i.castSucc (r (y i.castSucc)),
      Cube.continuous_update _ (by fun_prop)⟩,
    fun y hy ↦ p.property.1 _ (by
      change Function.update y i.castSucc (r (y i.castSucc)) ∈ ∂I^(n + 1)
      by_cases hyi : y i.castSucc = 0 ∨ y i.castSucc = 1
      · rcases hyi with hi | hi
        · rw [hi, hzero, ← hi, Function.update_eq_self]
          exact hy
        · rw [hi, hone, ← hi, Function.update_eq_self]
          exact hy
      · exact Cube.update_mem_boundary hy hyi _),
    fun y hy ↦ p.property.2 _ (by
      change Function.update y i.castSucc (r (y i.castSucc)) ∈ ⊔I^(n + 1)
      by_cases hyi : y i.castSucc = 0 ∨ y i.castSucc = 1
      · rcases hyi with hi | hi
        · rw [hi, hzero, ← hi, Function.update_eq_self]
          exact hy
        · rw [hi, hone, ← hi, Function.update_eq_self]
          exact hy
      · exact Cube.update_mem_boundaryJar (Fin.castSucc_ne_last i) hy hyi _)⟩

@[simp]
theorem reparamAt_apply (i : Fin n) (r : C(I, I)) (hzero : r 0 = 0) (hone : r 1 = 1)
    (p : RelGenLoop (n + 1) X A a) (y : I^Fin (n + 1)) :
    (reparamAt i r hzero hone p).val y =
      p.val (Function.update y i.castSucc (r (y i.castSucc))) :=
  rfl

/-- Any endpoint-fixing coordinate reparametrisation is relatively homotopic to the original
loop. -/
theorem homotopic_reparamAt (i : Fin n) (r : C(I, I)) (hzero : r 0 = 0) (hone : r 1 = 1)
    (p : RelGenLoop (n + 1) X A a) :
    _root_.RelGenLoop.Homotopic p (reparamAt i r hzero hone p) := by
  refine ⟨{
    toFun := fun sy ↦ p.val (Function.update sy.2 i.castSucc
      (Set.Icc.convexComb (sy.2 i.castSucc) (r (sy.2 i.castSucc)) sy.1))
    continuous_toFun := p.val.continuous.comp' (by
      apply continuous_pi
      intro k
      rcases eq_or_ne k i.castSucc with rfl | hk
      · simpa only [Function.update_self] using (by fun_prop :
          Continuous fun sy : I × (I^Fin (n + 1)) ↦
            Set.Icc.convexComb (sy.2 i.castSucc) (r (sy.2 i.castSucc)) sy.1)
      · simpa only [Function.update_of_ne hk] using (by fun_prop :
          Continuous fun sy : I × (I^Fin (n + 1)) ↦ sy.2 k))
    map_zero_left := fun y ↦ by simp
    map_one_left := fun y ↦ by rw [reparamAt_apply, Set.Icc.convexComb_one]
    prop' := fun s ↦ ⟨
      fun y hy ↦ p.property.1 _ (by
        change Function.update y i.castSucc
          (Set.Icc.convexComb (y i.castSucc) (r (y i.castSucc)) s) ∈ ∂I^(n + 1)
        by_cases hyi : y i.castSucc = 0 ∨ y i.castSucc = 1
        · rcases hyi with hi | hi
          · rw [hi, hzero, Set.Icc.convexComb_eq, ← hi, Function.update_eq_self]
            exact hy
          · rw [hi, hone, Set.Icc.convexComb_eq, ← hi, Function.update_eq_self]
            exact hy
        · exact Cube.update_mem_boundary hy hyi _),
      fun y hy ↦ p.property.2 _ (by
        change Function.update y i.castSucc
          (Set.Icc.convexComb (y i.castSucc) (r (y i.castSucc)) s) ∈ ⊔I^(n + 1)
        by_cases hyi : y i.castSucc = 0 ∨ y i.castSucc = 1
        · rcases hyi with hi | hi
          · rw [hi, hzero, Set.Icc.convexComb_eq, ← hi, Function.update_eq_self]
            exact hy
          · rw [hi, hone, Set.Icc.convexComb_eq, ← hi, Function.update_eq_self]
            exact hy
        · exact Cube.update_mem_boundaryJar (Fin.castSucc_ne_last i) hy hyi _)
      ⟩ }⟩

/-- The left summand of plateau concatenation, extended constantly across the remaining
two-thirds of the source cube. -/
def leftPlateauAt (i : Fin n) (p : RelGenLoop (n + 1) X A a) :
    RelGenLoop (n + 1) X A a :=
  ⟨p.val.comp ⟨fun y ↦ Function.update y i.castSucc (leftPlateauParam (y i.castSucc)),
      Cube.continuous_update _ (by fun_prop)⟩,
    fun y hy ↦ p.property.1 _ (by
      change Function.update y i.castSucc (leftPlateauParam (y i.castSucc)) ∈ ∂I^(n + 1)
      by_cases hyi : y i.castSucc = 0 ∨ y i.castSucc = 1
      · rcases hyi with hi | hi
        · rw [hi, leftPlateauParam_zero, ← hi, Function.update_eq_self]
          exact hy
        · rw [hi, leftPlateauParam_one, ← hi, Function.update_eq_self]
          exact hy
      · exact Cube.update_mem_boundary hy hyi _),
    fun y hy ↦ p.property.2 _ (by
      change Function.update y i.castSucc (leftPlateauParam (y i.castSucc)) ∈ ⊔I^(n + 1)
      by_cases hyi : y i.castSucc = 0 ∨ y i.castSucc = 1
      · rcases hyi with hi | hi
        · rw [hi, leftPlateauParam_zero, ← hi, Function.update_eq_self]
          exact hy
        · rw [hi, leftPlateauParam_one, ← hi, Function.update_eq_self]
          exact hy
      · exact Cube.update_mem_boundaryJar (Fin.castSucc_ne_last i) hy hyi _)⟩

/-- The right summand of plateau concatenation, extended constantly across the first
two-thirds of the source cube. -/
def rightPlateauAt (i : Fin n) (p : RelGenLoop (n + 1) X A a) :
    RelGenLoop (n + 1) X A a :=
  ⟨p.val.comp ⟨fun y ↦ Function.update y i.castSucc (rightPlateauParam (y i.castSucc)),
      Cube.continuous_update _ (by fun_prop)⟩,
    fun y hy ↦ p.property.1 _ (by
      change Function.update y i.castSucc (rightPlateauParam (y i.castSucc)) ∈ ∂I^(n + 1)
      by_cases hyi : y i.castSucc = 0 ∨ y i.castSucc = 1
      · rcases hyi with hi | hi
        · rw [hi, rightPlateauParam_zero, ← hi, Function.update_eq_self]
          exact hy
        · rw [hi, rightPlateauParam_one, ← hi, Function.update_eq_self]
          exact hy
      · exact Cube.update_mem_boundary hy hyi _),
    fun y hy ↦ p.property.2 _ (by
      change Function.update y i.castSucc (rightPlateauParam (y i.castSucc)) ∈ ⊔I^(n + 1)
      by_cases hyi : y i.castSucc = 0 ∨ y i.castSucc = 1
      · rcases hyi with hi | hi
        · rw [hi, rightPlateauParam_zero, ← hi, Function.update_eq_self]
          exact hy
        · rw [hi, rightPlateauParam_one, ← hi, Function.update_eq_self]
          exact hy
      · exact Cube.update_mem_boundaryJar (Fin.castSucc_ne_last i) hy hyi _)⟩

@[simp]
theorem leftPlateauAt_apply (i : Fin n) (p : RelGenLoop (n + 1) X A a)
    (y : I^Fin (n + 1)) :
    (leftPlateauAt i p).val y =
      p.val (Function.update y i.castSucc (leftPlateauParam (y i.castSucc))) :=
  rfl

@[simp]
theorem rightPlateauAt_apply (i : Fin n) (p : RelGenLoop (n + 1) X A a)
    (y : I^Fin (n + 1)) :
    (rightPlateauAt i p).val y =
      p.val (Function.update y i.castSucc (rightPlateauParam (y i.castSucc))) :=
  rfl

/-- The extended left summand is relatively homotopic to the original left loop. -/
theorem homotopic_leftPlateauAt (i : Fin n) (p : RelGenLoop (n + 1) X A a) :
    _root_.RelGenLoop.Homotopic p (leftPlateauAt i p) := by
  let r : C(I, I) := ⟨leftPlateauParam, continuous_leftPlateauParam⟩
  have H := homotopic_reparamAt i r leftPlateauParam_zero leftPlateauParam_one p
  have heq : leftPlateauAt i p =
      reparamAt i r leftPlateauParam_zero leftPlateauParam_one p := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro y
    rfl
  rw [heq]
  exact H

/-- The extended right summand is relatively homotopic to the original right loop. -/
theorem homotopic_rightPlateauAt (i : Fin n) (p : RelGenLoop (n + 1) X A a) :
    _root_.RelGenLoop.Homotopic p (rightPlateauAt i p) := by
  let r : C(I, I) := ⟨rightPlateauParam, continuous_rightPlateauParam⟩
  have H := homotopic_reparamAt i r rightPlateauParam_zero rightPlateauParam_one p
  have heq : rightPlateauAt i p =
      reparamAt i r rightPlateauParam_zero rightPlateauParam_one p := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro y
    rfl
  rw [heq]
  exact H

/-- On the left plateau region, concatenation is the extended left summand. -/
theorem plateauTransAt_eq_left (i : Fin n) (p q : RelGenLoop (n + 1) X A a)
    (y : I^Fin (n + 1)) (hy : (y i.castSucc : ℝ) ≤ 2 / 3) :
    (plateauTransAt i p q).val y = (leftPlateauAt i p).val y := by
  rw [plateauTransAt, pauseAt_apply, _root_.RelGenLoop.transAt_apply,
    leftPlateauAt_apply]
  simp only [Function.update_self, Function.update_idem]
  rw [if_pos (middleThirdPause_le_half hy)]
  rfl

/-- On the left plateau region, the extended right summand is the constant basepoint. -/
theorem rightPlateauAt_eq_base (i : Fin n) (p : RelGenLoop (n + 1) X A a)
    (y : I^Fin (n + 1)) (hy : (y i.castSucc : ℝ) ≤ 2 / 3) :
    (rightPlateauAt i p).val y = a := by
  rw [rightPlateauAt_apply, rightPlateauParam_eq_zero hy]
  exact p.property.2 _ (_root_.RelGenLoop.update_castSucc_zero_mem_boundaryJar i y)

/-- On the right plateau region, concatenation is the extended right summand. -/
theorem plateauTransAt_eq_right (i : Fin n) (p q : RelGenLoop (n + 1) X A a)
    (y : I^Fin (n + 1)) (hy : 1 / 3 ≤ (y i.castSucc : ℝ)) :
    (plateauTransAt i p q).val y = (rightPlateauAt i q).val y := by
  rw [plateauTransAt, pauseAt_apply, _root_.RelGenLoop.transAt_apply,
    rightPlateauAt_apply]
  simp only [Function.update_self, Function.update_idem]
  by_cases hle : (middleThirdPause (y i.castSucc) : ℝ) ≤ 1 / 2
  · have heq : (middleThirdPause (y i.castSucc) : ℝ) = 1 / 2 :=
      le_antisymm hle (half_le_middleThirdPause hy)
    rw [if_pos hle, _root_.RelGenLoop.firstHalf_of_half heq,
      rightPlateauParam, _root_.RelGenLoop.secondHalf_of_half heq]
    exact _root_.RelGenLoop.transAt_wall i p q y
  · rw [if_neg hle]
    rfl

/-- On the right plateau region, the extended left summand is the constant basepoint. -/
theorem leftPlateauAt_eq_base (i : Fin n) (p : RelGenLoop (n + 1) X A a)
    (y : I^Fin (n + 1)) (hy : 1 / 3 ≤ (y i.castSucc : ℝ)) :
    (leftPlateauAt i p).val y = a := by
  rw [leftPlateauAt_apply, leftPlateauParam_eq_one hy]
  exact p.property.2 _ (_root_.RelGenLoop.update_castSucc_one_mem_boundaryJar i y)

end RelGenLoop

/-! ### The subordinate cover of the source cube -/

/-- Cover the cube by left and right regions.  Their overlap lies in the constant middle third
of plateau concatenation. -/
def plateauCubeCover (n : ℕ) : Bool → Set (I^Fin (n + 2)) := Bool.rec
  ({y | (y 0 : ℝ) < 2 / 3})
  ({y | 1 / 3 < (y 0 : ℝ)})

/-- The interiors of the two plateau regions cover the cube. -/
theorem plateauCubeCover_condition (n : ℕ) :
    TopCat.SmallSimplicesCondition (X := TopCat.of (I^Fin (n + 2)))
      (plateauCubeCover n) := by
  let L : Set (I^Fin (n + 2)) := {y | (y 0 : ℝ) < 2 / 3}
  let R : Set (I^Fin (n + 2)) := {y | 1 / 3 < (y 0 : ℝ)}
  have hLopen : IsOpen L := by
    exact isOpen_lt
      (continuous_subtype_val.comp (continuous_apply (0 : Fin (n + 2)))) continuous_const
  have hRopen : IsOpen R := by
    exact isOpen_lt continuous_const
      (continuous_subtype_val.comp (continuous_apply (0 : Fin (n + 2))))
  have hLint : L ⊆ interior (plateauCubeCover n false) := by
    exact interior_maximal (by intro y hy; exact hy) hLopen
  have hRint : R ⊆ interior (plateauCubeCover n true) := by
    exact interior_maximal (by intro y hy; exact hy) hRopen
  constructor
  apply Set.eq_univ_of_forall
  intro y
  rw [Set.mem_iUnion]
  by_cases hy : (y 0 : ℝ) < 2 / 3
  · exact ⟨false, hLint hy⟩
  · refine ⟨true, hRint ?_⟩
    dsimp [R]
    linarith

/-! ### Local chain identity -/

/-- Relative chains of the cube pair subordinate to the plateau cover. -/
abbrev plateauCoveredRelativeComplex (n : ℕ) :=
  coveredRelativeComplex (X := TopCat.of (I^Fin (n + 2)))
    (plateauCubeCover n) (∂I^(n + 2))

/-- Projection from subordinate absolute chains to subordinate relative chains. -/
noncomputable def plateauCoveredProjection (n : ℕ) :
    (TopCat.toSSet.subcomplexOfSets
      (X := TopCat.of (I^Fin (n + 2))) (plateauCubeCover n)).toSSet.chainComplex
        (AddCommGrpCat.of ℤ) ⟶
      coveredRelativeComplex (X := TopCat.of (I^Fin (n + 2)))
        (plateauCubeCover n) (∂I^(n + 2)) :=
  cokernel.π (SSet.chainComplexMap
    (coveredSubspaceMap (X := TopCat.of (I^Fin (n + 2)))
      (plateauCubeCover n) (∂I^(n + 2))) (AddCommGrpCat.of ℤ))

@[reassoc (attr := simp)]
theorem plateauCoveredProjection_comp_inclusion (n : ℕ) :
    plateauCoveredProjection n ≫
        coveredRelativeInclusion (X := TopCat.of (I^Fin (n + 2)))
          (plateauCubeCover n) (∂I^(n + 2)) =
      SSet.chainComplexMap (TopCat.toSSet.subcomplexOfSets
          (X := TopCat.of (I^Fin (n + 2))) (plateauCubeCover n)).ι
          (AddCommGrpCat.of ℤ) ≫
        relProj (subIncl (Y := TopCat.of (I^Fin (n + 2))) (∂I^(n + 2))) := by
  unfold plateauCoveredProjection
  exact coveredRelative_π_inclusion (X := TopCat.of (I^Fin (n + 2)))
    (plateauCubeCover n) (∂I^(n + 2))

/-- Map subordinate relative chains along a relative cubical loop. -/
noncomputable def plateauCoveredMap (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p : RelGenLoop (n + 2) X A a) :
    coveredRelativeComplex (X := TopCat.of (I^Fin (n + 2)))
        (plateauCubeCover n) (∂I^(n + 2)) ⟶
      relComplex (subIncl (Y := TopCat.of X) A) :=
  coveredRelativeInclusion (X := TopCat.of (I^Fin (n + 2)))
      (plateauCubeCover n) (∂I^(n + 2)) ≫
    relComplexMap
      (subIncl (Y := TopCat.of (I^Fin (n + 2))) (∂I^(n + 2)))
      (subIncl (Y := TopCat.of X) A)
      (RelGenLoop.pairMap p).subIncl_naturality

attribute [local implicit_reducible] relComplex Hrel

/-- Map subordinate absolute chains along a relative loop and project to target relative
chains. -/
noncomputable def plateauSmallMap (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p : RelGenLoop (n + 2) X A a) :
    (TopCat.toSSet.subcomplexOfSets
      (X := TopCat.of (I^Fin (n + 2))) (plateauCubeCover n)).toSSet.chainComplex
        (AddCommGrpCat.of ℤ) ⟶
      relComplex (subIncl (Y := TopCat.of X) A) :=
  SSet.chainComplexMap (TopCat.toSSet.subcomplexOfSets
      (X := TopCat.of (I^Fin (n + 2))) (plateauCubeCover n)).ι
      (AddCommGrpCat.of ℤ) ≫
    CsingMap (RelGenLoop.pairMap p).ambientHom ≫
      relProj (subIncl (Y := TopCat.of X) A)

/-- The subordinate relative projection followed by `plateauCoveredMap` is the corresponding
map on subordinate absolute chains. -/
theorem plateauCoveredProjection_comp_map (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p : RelGenLoop (n + 2) X A a) :
    plateauCoveredProjection n ≫ plateauCoveredMap n p = plateauSmallMap n p := by
  unfold plateauCoveredMap plateauSmallMap
  rw [← Category.assoc, plateauCoveredProjection_comp_inclusion, Category.assoc]
  rw [relProj_comp_relComplexMap]

/-- On a subordinate singular summand, `plateauSmallMap` is postcomposition followed by the
target relative projection. -/
theorem plateauSmallMap_ι (n k : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p : RelGenLoop (n + 2) X A a)
    (s : (TopCat.toSSet.subcomplexOfSets (X := TopCat.of (I^Fin (n + 2)))
      (plateauCubeCover n) : SSet) _⦋k⦌) :
    (TopCat.toSSet.subcomplexOfSets (X := TopCat.of (I^Fin (n + 2)))
        (plateauCubeCover n) : SSet).ιChainComplex s ≫
        (plateauSmallMap n p).f k =
      (TopCat.of X).ιSingularChainComplex
          ((TopCat.toSSet.map (RelGenLoop.pairMap p).ambientHom).app _ s.1) ≫
        (relProj (subIncl (Y := TopCat.of X) A)).f k := by
  unfold plateauSmallMap
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    SSet.ι_chainComplexMap_f_assoc]
  change (TopCat.of (I^Fin (n + 2))).ιSingularChainComplex s.1 ≫
      (TopCat.singularChainComplexMap (RelGenLoop.pairMap p).ambientHom
        (AddCommGrpCat.of ℤ)).f k ≫
        (relProj (subIncl (Y := TopCat.of X) A)).f k = _
  rw [TopCat.ι_singularChainComplexMap_assoc]

/-- On a simplex contained in the left cover member, the plateau map and left extended map
induce the same singular simplex. -/
theorem plateau_singular_eq_left_of_mem {n k : ℕ}
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p q : RelGenLoop (n + 2) X A a)
    (s : Sng (TopCat.of (I^Fin (n + 2))) _⦋k⦌)
    (hs : Set.range (sngEquiv (TopCat.of (I^Fin (n + 2))) k s) ⊆
      plateauCubeCover n false) :
    (TopCat.toSSet.map (RelGenLoop.pairMap (RelGenLoop.plateauTransAt 0 p q)).ambientHom).app _ s =
      (TopCat.toSSet.map (RelGenLoop.pairMap (RelGenLoop.leftPlateauAt 0 p)).ambientHom).app _ s := by
  apply sng_ext
  intro z
  rw [sngEquiv_map, sngEquiv_map]
  exact RelGenLoop.plateauTransAt_eq_left 0 p q _
    (le_of_lt (hs (Set.mem_range_self z)))

/-- On a simplex contained in the left cover member, the right extended map is the constant
simplex at the basepoint. -/
theorem right_singular_eq_const_of_mem_left {n k : ℕ}
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (q : RelGenLoop (n + 2) X A a)
    (s : Sng (TopCat.of (I^Fin (n + 2))) _⦋k⦌)
    (hs : Set.range (sngEquiv (TopCat.of (I^Fin (n + 2))) k s) ⊆
      plateauCubeCover n false) :
    (TopCat.toSSet.map (RelGenLoop.pairMap (RelGenLoop.rightPlateauAt 0 q)).ambientHom).app _ s =
      constSimplex (X := TopCat.of X) k a := by
  apply sng_ext
  intro z
  rw [sngEquiv_map, constSimplex, sngEquiv_sng]
  exact RelGenLoop.rightPlateauAt_eq_base 0 q _
    (le_of_lt (hs (Set.mem_range_self z)))

/-- On a simplex contained in the right cover member, the plateau map and right extended map
induce the same singular simplex. -/
theorem plateau_singular_eq_right_of_mem {n k : ℕ}
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p q : RelGenLoop (n + 2) X A a)
    (s : Sng (TopCat.of (I^Fin (n + 2))) _⦋k⦌)
    (hs : Set.range (sngEquiv (TopCat.of (I^Fin (n + 2))) k s) ⊆
      plateauCubeCover n true) :
    (TopCat.toSSet.map (RelGenLoop.pairMap (RelGenLoop.plateauTransAt 0 p q)).ambientHom).app _ s =
      (TopCat.toSSet.map (RelGenLoop.pairMap (RelGenLoop.rightPlateauAt 0 q)).ambientHom).app _ s := by
  apply sng_ext
  intro z
  rw [sngEquiv_map, sngEquiv_map]
  exact RelGenLoop.plateauTransAt_eq_right 0 p q _
    (le_of_lt (hs (Set.mem_range_self z)))

/-- On a simplex contained in the right cover member, the left extended map is the constant
simplex at the basepoint. -/
theorem left_singular_eq_const_of_mem_right {n k : ℕ}
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p : RelGenLoop (n + 2) X A a)
    (s : Sng (TopCat.of (I^Fin (n + 2))) _⦋k⦌)
    (hs : Set.range (sngEquiv (TopCat.of (I^Fin (n + 2))) k s) ⊆
      plateauCubeCover n true) :
    (TopCat.toSSet.map (RelGenLoop.pairMap (RelGenLoop.leftPlateauAt 0 p)).ambientHom).app _ s =
      constSimplex (X := TopCat.of X) k a := by
  apply sng_ext
  intro z
  rw [sngEquiv_map, constSimplex, sngEquiv_sng]
  exact RelGenLoop.leftPlateauAt_eq_base 0 p _
    (le_of_lt (hs (Set.mem_range_self z)))

/-- A constant singular simplex at a point of the subspace vanishes in relative chains. -/
theorem relProj_gen_constSimplex (k : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} (a : A) :
    (relProj (subIncl (Y := TopCat.of X) A)).f k
        (gen (constSimplex (X := TopCat.of X) k a)) = 0 := by
  have hconst :
      (sngIncl A).app _ (constSimplex (X := TopCat.of A) k a) =
        constSimplex (X := TopCat.of X) k a := by
    rfl
  rw [← hconst, ← CsingMap_gen, ← ConcreteCategory.comp_apply,
    CsingMap_comp_relProj_f, zero_hom_apply]

/-- Categorical form of `relProj_gen_constSimplex`. -/
theorem ι_constSimplex_comp_relProj (k : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} (a : A) :
    (TopCat.of X).ιSingularChainComplex
        (constSimplex (X := TopCat.of X) k a) ≫
      (relProj (subIncl (Y := TopCat.of X) A)).f k = 0 := by
  apply intHom_ext
  change (relProj (subIncl (Y := TopCat.of X) A)).f k
      (gen (constSimplex (X := TopCat.of X) k a)) = 0
  exact relProj_gen_constSimplex k a

set_option maxHeartbeats 1000000 in
/-- On a subordinate generator, plateau concatenation is the sum of its left and right extended
summands. -/
theorem plateauSmallMap_ι_eq_add (n k : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p q : RelGenLoop (n + 2) X A a)
    (s : (TopCat.toSSet.subcomplexOfSets (X := TopCat.of (I^Fin (n + 2)))
      (plateauCubeCover n) : SSet) _⦋k⦌) :
    (TopCat.toSSet.subcomplexOfSets (X := TopCat.of (I^Fin (n + 2)))
        (plateauCubeCover n) : SSet).ιChainComplex s ≫
        (plateauSmallMap n (RelGenLoop.plateauTransAt 0 p q)).f k =
      (TopCat.toSSet.subcomplexOfSets (X := TopCat.of (I^Fin (n + 2)))
          (plateauCubeCover n) : SSet).ιChainComplex s ≫
          (plateauSmallMap n (RelGenLoop.leftPlateauAt 0 p)).f k +
        (TopCat.toSSet.subcomplexOfSets (X := TopCat.of (I^Fin (n + 2)))
          (plateauCubeCover n) : SSet).ιChainComplex s ≫
          (plateauSmallMap n (RelGenLoop.rightPlateauAt 0 q)).f k := by
  rw [plateauSmallMap_ι, plateauSmallMap_ι, plateauSmallMap_ι]
  obtain ⟨b, hb⟩ := (TopCat.toSSet.mem_subcomplexOfSets_iff
    (X := TopCat.of (I^Fin (n + 2))) (U := plateauCubeCover n) s.1).1 s.2
  cases b with
  | false =>
      rw [plateau_singular_eq_left_of_mem p q s.1 hb,
        right_singular_eq_const_of_mem_left q s.1 hb,
        ι_constSimplex_comp_relProj]
      simp
  | true =>
      rw [plateau_singular_eq_right_of_mem p q s.1 hb,
        left_singular_eq_const_of_mem_right p s.1 hb,
        ι_constSimplex_comp_relProj]
      simp

/-- On subordinate chains, plateau concatenation is the sum of its left and right extended
summands. -/
theorem plateauSmallMap_eq_add (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p q : RelGenLoop (n + 2) X A a) :
    plateauSmallMap n (RelGenLoop.plateauTransAt 0 p q) =
      plateauSmallMap n (RelGenLoop.leftPlateauAt 0 p) +
        plateauSmallMap n (RelGenLoop.rightPlateauAt 0 q) := by
  apply HomologicalComplex.hom_ext
  intro k
  apply SSet.chainComplex_hom_ext
  intro s
  change _ ≫ (plateauSmallMap n (RelGenLoop.plateauTransAt 0 p q)).f k =
    _ ≫ ((plateauSmallMap n (RelGenLoop.leftPlateauAt 0 p)).f k +
      (plateauSmallMap n (RelGenLoop.rightPlateauAt 0 q)).f k)
  rw [Preadditive.comp_add]
  exact plateauSmallMap_ι_eq_add n k p q s

/-- The local plateau decomposition descends to subordinate relative chains. -/
theorem plateauCoveredMap_eq_add (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p q : RelGenLoop (n + 2) X A a) :
    plateauCoveredMap n (RelGenLoop.plateauTransAt 0 p q) =
      plateauCoveredMap n (RelGenLoop.leftPlateauAt 0 p) +
        plateauCoveredMap n (RelGenLoop.rightPlateauAt 0 q) := by
  haveI : Epi (plateauCoveredProjection n) := by
    unfold plateauCoveredProjection
    exact coequalizer.π_epi
  refine (cancel_epi (plateauCoveredProjection n)).1 ?_
  rw [Preadditive.comp_add, plateauCoveredProjection_comp_map,
    plateauCoveredProjection_comp_map, plateauCoveredProjection_comp_map,
    plateauSmallMap_eq_add]

/-! ### Passage to relative homology -/

/-- The small-simplices isomorphism for the plateau cover in top degree. -/
noncomputable def plateauCoveredTopHomologyIso (n : ℕ) :
    (plateauCoveredRelativeComplex n).homology (n + 2) ≅
      HrelSet (Y := TopCat.of (I^Fin (n + 2))) (n + 2) (∂I^(n + 2)) := by
  letI : IsIso (HomologicalComplex.homologyMap
      (coveredRelativeInclusion (X := TopCat.of (I^Fin (n + 2)))
        (plateauCubeCover n) (∂I^(n + 2))) (n + 2)) :=
    isIso_homologyMap_coveredRelativeInclusion
      (X := TopCat.of (I^Fin (n + 2))) (plateauCubeCover n) (∂I^(n + 2))
      (plateauCubeCover_condition n) (n + 2)
  exact asIso (HomologicalComplex.homologyMap
    (coveredRelativeInclusion (X := TopCat.of (I^Fin (n + 2)))
      (plateauCubeCover n) (∂I^(n + 2))) (n + 2))

/-- The oriented cube class, represented in relative chains subordinate to the plateau cover. -/
noncomputable def plateauCoveredFundamentalClass (n : ℕ) :
    (plateauCoveredRelativeComplex n).homology (n + 2) :=
  (plateauCoveredTopHomologyIso n).inv (cubePairFundamentalClass n)

@[simp]
theorem plateauCoveredTopHomologyIso_fundamentalClass (n : ℕ) :
    (plateauCoveredTopHomologyIso n).hom (plateauCoveredFundamentalClass n) =
      cubePairFundamentalClass n := by
  simp [plateauCoveredFundamentalClass]

/-- Evaluating a relative loop on the subordinate fundamental class agrees with its ordinary
relative-homology evaluation on the cube fundamental class. -/
theorem homologyMap_plateauCoveredMap_fundamentalClass (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p : RelGenLoop (n + 2) X A a) :
    HomologicalComplex.homologyMap (plateauCoveredMap n p) (n + 2)
        (plateauCoveredFundamentalClass n) =
      RelGenLoop.hrelMap (n + 2) p (cubePairFundamentalClass n) := by
  unfold plateauCoveredMap
  rw [HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply]
  rw [show HomologicalComplex.homologyMap
      (coveredRelativeInclusion (X := TopCat.of (I^Fin (n + 2)))
        (plateauCubeCover n) (∂I^(n + 2))) (n + 2)
        (plateauCoveredFundamentalClass n) = cubePairFundamentalClass n from
      plateauCoveredTopHomologyIso_fundamentalClass n]
  rfl

/-- Plateau concatenation evaluates on the fundamental class as the sum of its two extended
pieces. -/
theorem hrelMap_plateauTransAt_fundamentalClass (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p q : RelGenLoop (n + 2) X A a) :
    RelGenLoop.hrelMap (n + 2) (RelGenLoop.plateauTransAt 0 p q)
        (cubePairFundamentalClass n) =
      RelGenLoop.hrelMap (n + 2) (RelGenLoop.leftPlateauAt 0 p)
          (cubePairFundamentalClass n) +
        RelGenLoop.hrelMap (n + 2) (RelGenLoop.rightPlateauAt 0 q)
          (cubePairFundamentalClass n) := by
  have hmap := congrArg
    (fun f : plateauCoveredRelativeComplex n ⟶
        relComplex (subIncl (Y := TopCat.of X) A) ↦
      HomologicalComplex.homologyMap f (n + 2))
    (plateauCoveredMap_eq_add n p q)
  have h := ConcreteCategory.congr_hom hmap (plateauCoveredFundamentalClass n)
  simpa only [HomologicalComplex.homologyMap_add, AddCommGrpCat.hom_add_apply,
    homologyMap_plateauCoveredMap_fundamentalClass] using h

/-- Cubical concatenation adds the relative-homology classes carried by its two factors. -/
theorem hrelMap_transAt_fundamentalClass (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p q : RelGenLoop (n + 2) X A a) :
    RelGenLoop.hrelMap (n + 2) (_root_.RelGenLoop.transAt 0 p q)
        (cubePairFundamentalClass n) =
      RelGenLoop.hrelMap (n + 2) p (cubePairFundamentalClass n) +
        RelGenLoop.hrelMap (n + 2) q (cubePairFundamentalClass n) := by
  have htrans := RelGenLoop.hrelMap_eq_of_homotopic
    (RelGenLoop.homotopic_plateauTransAt 0 p q) (n + 2)
  have hleft := RelGenLoop.hrelMap_eq_of_homotopic
    (RelGenLoop.homotopic_leftPlateauAt 0 p) (n + 2)
  have hright := RelGenLoop.hrelMap_eq_of_homotopic
    (RelGenLoop.homotopic_rightPlateauAt 0 q) (n + 2)
  calc
    _ = RelGenLoop.hrelMap (n + 2) (RelGenLoop.plateauTransAt 0 p q)
          (cubePairFundamentalClass n) :=
      ConcreteCategory.congr_hom htrans (cubePairFundamentalClass n)
    _ = RelGenLoop.hrelMap (n + 2) (RelGenLoop.leftPlateauAt 0 p)
          (cubePairFundamentalClass n) +
        RelGenLoop.hrelMap (n + 2) (RelGenLoop.rightPlateauAt 0 q)
          (cubePairFundamentalClass n) :=
      hrelMap_plateauTransAt_fundamentalClass n p q
    _ = _ := congrArg₂ (fun x y ↦ x + y)
      (ConcreteCategory.congr_hom hleft (cubePairFundamentalClass n)).symm
      (ConcreteCategory.congr_hom hright (cubePairFundamentalClass n)).symm

/-! ### The relative Hurewicz homomorphism -/

/-- The relative Hurewicz comparison carries multiplication of relative homotopy classes to
addition in relative homology. -/
theorem relativeHurewicz_mul (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (x y : π_rel (n + 2) X A a) :
    relativeHurewicz n A a (x * y) =
      relativeHurewicz n A a x + relativeHurewicz n A a y := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  rw [RelHomotopyGroup.mul_mk (0 : Fin (n + 1)), relativeHurewicz_mk,
    relativeHurewicz_mk, relativeHurewicz_mk,
    hrelMap_transAt_fundamentalClass]
  exact add_comm _ _

/-- The relative Hurewicz comparison sends the constant relative class to zero. -/
@[simp]
theorem relativeHurewicz_one (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A} :
    relativeHurewicz n A a (1 : π_rel (n + 2) X A a) = 0 := by
  have h := relativeHurewicz_mul n (A := A) (a := a)
    (1 : π_rel (n + 2) X A a) 1
  rw [one_mul] at h
  apply add_left_cancel (a := relativeHurewicz n A a
    (1 : π_rel (n + 2) X A a))
  simpa only [add_zero] using h.symm

/-- The relative Hurewicz comparison as an additive homomorphism after applying the additive
type tag to the relative homotopy group. -/
noncomputable def relativeHurewiczAdd (n : ℕ)
    {X : Type} [TopologicalSpace X] (A : Set X) (a : A) :
    Additive (π_rel (n + 2) X A a) →+
      HrelSet (Y := TopCat.of X) (n + 2) A where
  toFun x := relativeHurewicz n A a x.toMul
  map_zero' := relativeHurewicz_one n
  map_add' x y := relativeHurewicz_mul n x.toMul y.toMul

@[simp]
theorem relativeHurewiczAdd_ofMul (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (x : π_rel (n + 2) X A a) :
    relativeHurewiczAdd n A a (Additive.ofMul x) = relativeHurewicz n A a x :=
  rfl

end Submission
