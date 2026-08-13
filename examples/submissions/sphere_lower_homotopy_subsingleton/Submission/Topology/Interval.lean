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

end TopCat.I
