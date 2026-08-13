/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# Lattice operations on the categorical unit interval

Continuous minimum and maximum maps on `TopCat.I` are convenient for collar contractions: maximum
pushes a cone coordinate toward its apex, while minimum pushes it toward its base.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

noncomputable section

namespace TopCat.I

universe u

/-- The categorical unit interval is compact. -/
noncomputable instance compactSpace : CompactSpace TopCat.I.{u} :=
  homeomorph.symm.compactSpace

/-- Continuous maximum on the categorical unit interval. -/
def max : TopCat.I.{u} ⊗ TopCat.I ⟶ TopCat.I :=
  TopCat.ofHom
    { toFun := fun p ↦ homeomorph.symm (Max.max (homeomorph p.1) (homeomorph p.2))
      continuous_toFun := by fun_prop }

@[simp]
theorem max_apply (s t : TopCat.I.{u}) :
    homeomorph (max (s, t)) = Max.max (homeomorph s) (homeomorph t) := rfl

@[simp]
theorem max_zero_right (s : TopCat.I.{u}) : max (s, 0) = s := by
  apply homeomorph.injective
  simp

@[simp]
theorem max_zero_left (s : TopCat.I.{u}) : max (0, s) = s := by
  apply homeomorph.injective
  simp

@[simp]
theorem max_comm (s t : TopCat.I.{u}) : max (s, t) = max (t, s) := by
  apply homeomorph.injective
  simp only [max_apply]
  exact _root_.max_comm _ _

@[simp]
theorem max_one_right (s : TopCat.I.{u}) : max (s, 1) = 1 := by
  apply homeomorph.injective
  rw [max_apply, homeomorph_one, max_eq_right]
  exact (homeomorph s).2.2

@[simp]
theorem max_one_left (s : TopCat.I.{u}) : max (1, s) = 1 := by
  apply homeomorph.injective
  rw [max_apply, homeomorph_one, max_eq_left]
  exact (homeomorph s).2.2

/-- Continuous minimum on the categorical unit interval. -/
def min : TopCat.I.{u} ⊗ TopCat.I ⟶ TopCat.I :=
  TopCat.ofHom
    { toFun := fun p ↦ homeomorph.symm (Min.min (homeomorph p.1) (homeomorph p.2))
      continuous_toFun := by fun_prop }

@[simp]
theorem min_apply (s t : TopCat.I.{u}) :
    homeomorph (min (s, t)) = Min.min (homeomorph s) (homeomorph t) := rfl

@[simp]
theorem min_one_right (s : TopCat.I.{u}) : min (s, 1) = s := by
  apply homeomorph.injective
  rw [min_apply, homeomorph_one, min_eq_left]
  exact (homeomorph s).2.2

@[simp]
theorem min_one_left (s : TopCat.I.{u}) : min (1, s) = s := by
  apply homeomorph.injective
  rw [min_apply, homeomorph_one, min_eq_right]
  exact (homeomorph s).2.2

@[simp]
theorem min_zero_right (s : TopCat.I.{u}) : min (s, 0) = 0 := by
  apply homeomorph.injective
  simp

@[simp]
theorem min_zero_left (s : TopCat.I.{u}) : min (0, s) = 0 := by
  apply homeomorph.injective
  simp

/-- Continuous multiplication on the categorical unit interval. -/
def mul : TopCat.I.{u} ⊗ TopCat.I ⟶ TopCat.I :=
  TopCat.ofHom
    { toFun := fun p ↦ homeomorph.symm ⟨
        (homeomorph p.1 : ℝ) * (homeomorph p.2 : ℝ), by
          constructor
          · exact mul_nonneg (homeomorph p.1).2.1 (homeomorph p.2).2.1
          · nlinarith [(homeomorph p.1).2.1, (homeomorph p.1).2.2,
              (homeomorph p.2).2.1, (homeomorph p.2).2.2] ⟩
      continuous_toFun := by fun_prop }

@[simp]
theorem mul_apply (s t : TopCat.I.{u}) :
    (homeomorph (mul (s, t)) : ℝ) =
      (homeomorph s : ℝ) * (homeomorph t : ℝ) := rfl

@[simp]
theorem mul_zero_right (s : TopCat.I.{u}) : mul (s, 0) = 0 := by
  apply homeomorph.injective
  apply Subtype.ext
  rw [mul_apply]
  simp

@[simp]
theorem mul_zero_left (s : TopCat.I.{u}) : mul (0, s) = 0 := by
  apply homeomorph.injective
  apply Subtype.ext
  rw [mul_apply]
  simp

@[simp]
theorem mul_one_right (s : TopCat.I.{u}) : mul (s, 1) = s := by
  apply homeomorph.injective
  apply Subtype.ext
  rw [mul_apply]
  simp

@[simp]
theorem mul_one_left (s : TopCat.I.{u}) : mul (1, s) = s := by
  apply homeomorph.injective
  apply Subtype.ext
  rw [mul_apply]
  simp

/-- The midpoint of the categorical unit interval. -/
def midpoint : TopCat.I.{u} :=
  homeomorph.symm ⟨1 / 2, by constructor <;> norm_num⟩

/-- Linear interpolation from the midpoint at time zero to the supplied interval coordinate at
time one. -/
def midpointLerp : TopCat.I.{u} ⊗ TopCat.I ⟶ TopCat.I :=
  TopCat.ofHom
    { toFun := fun p ↦ homeomorph.symm ⟨
        (1 - (homeomorph p.2 : ℝ)) / 2 +
          (homeomorph p.2 : ℝ) * (homeomorph p.1 : ℝ), by
        constructor
        · have hmul : 0 ≤ (homeomorph p.2 : ℝ) * (homeomorph p.1 : ℝ) :=
            mul_nonneg (homeomorph p.2).2.1 (homeomorph p.1).2.1
          nlinarith [(homeomorph p.2).2.2]
        · have hmul : (homeomorph p.2 : ℝ) * (homeomorph p.1 : ℝ) ≤
              (homeomorph p.2 : ℝ) :=
            mul_le_of_le_one_right (homeomorph p.2).2.1 (homeomorph p.1).2.2
          nlinarith [(homeomorph p.2).2.2]⟩
      continuous_toFun := by fun_prop }

@[simp]
theorem midpointLerp_apply (s t : TopCat.I.{u}) :
    (homeomorph (midpointLerp (s, t)) : ℝ) =
      (1 - (homeomorph t : ℝ)) / 2 +
        (homeomorph t : ℝ) * (homeomorph s : ℝ) := rfl

@[simp]
theorem midpointLerp_zero (s : TopCat.I.{u}) : midpointLerp (s, 0) = midpoint := by
  apply homeomorph.injective
  apply Subtype.ext
  rw [midpointLerp_apply]
  simp [midpoint]

@[simp]
theorem midpointLerp_one (s : TopCat.I.{u}) : midpointLerp (s, 1) = s := by
  apply homeomorph.injective
  apply Subtype.ext
  rw [midpointLerp_apply]
  simp

/-- Interpolating a point of `(1/3, 2/3)` with the midpoint stays in that open interval. -/
theorem midpointLerp_mem_thirds (s t : TopCat.I.{u})
    (hsl : 1 / 3 < (homeomorph s : ℝ))
    (hsu : (homeomorph s : ℝ) < 2 / 3) :
    1 / 3 < (homeomorph (midpointLerp (s, t)) : ℝ) ∧
      (homeomorph (midpointLerp (s, t)) : ℝ) < 2 / 3 := by
  rw [midpointLerp_apply]
  constructor
  · have hmul : 0 ≤ (homeomorph t : ℝ) *
        ((homeomorph s : ℝ) - 1 / 3) :=
      mul_nonneg (homeomorph t).2.1 (by linarith)
    have hbase : 0 ≤ (1 - (homeomorph t : ℝ)) * (1 / 2 - 1 / 3) :=
      mul_nonneg (by linarith [(homeomorph t).2.2]) (by norm_num)
    by_cases ht : (homeomorph t : ℝ) = 0
    · rw [ht]
      norm_num
    · have ht' : 0 < (homeomorph t : ℝ) :=
        lt_of_le_of_ne (homeomorph t).2.1 (Ne.symm ht)
      have hmul' : 0 < (homeomorph t : ℝ) *
          ((homeomorph s : ℝ) - 1 / 3) := mul_pos ht' (by linarith)
      nlinarith
  · have hmul : 0 ≤ (homeomorph t : ℝ) *
        (2 / 3 - (homeomorph s : ℝ)) :=
      mul_nonneg (homeomorph t).2.1 (by linarith)
    have hbase : 0 ≤ (1 - (homeomorph t : ℝ)) * (2 / 3 - 1 / 2) :=
      mul_nonneg (by linarith [(homeomorph t).2.2]) (by norm_num)
    by_cases ht : (homeomorph t : ℝ) = 1
    · rw [ht]
      simpa using hsu
    · have ht' : 0 < 1 - (homeomorph t : ℝ) :=
        sub_pos.mpr (lt_of_le_of_ne (homeomorph t).2.2 ht)
      have hbase' : 0 < (1 - (homeomorph t : ℝ)) * (2 / 3 - 1 / 2) :=
        mul_pos ht' (by norm_num)
      nlinarith

end TopCat.I
