/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Mathlib.Algebra.Homology.Homotopy

/-!
# ...

-/

@[expose] public section

open CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C]

namespace Homotopy

section

variable {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}
  {f g : K ⟶ L}

lemma sub_eq_nullHomotopicMap (h : Homotopy f g) :
    f - g = nullHomotopicMap h.hom := by
  ext n
  simp [nullHomotopicMap, HomologicalComplex.sub_f_apply, h.comm]

lemma eq_add_nullHomotopicMap (h : Homotopy f g) :
    f = g + nullHomotopicMap h.hom := by
  simp [← h.sub_eq_nullHomotopicMap]

lemma eq_sub_nullHomotopicMap (h : Homotopy f g) :
    g = f - nullHomotopicMap h.hom := by
  simp [← h.sub_eq_nullHomotopicMap]

@[simp]
lemma nullHomotopicMap_add (h₁ : ∀ i j, K.X i ⟶ L.X j) (h₂ : ∀ i j, K.X i ⟶ L.X j) :
    nullHomotopicMap (h₁ + h₂) = nullHomotopicMap h₁ + nullHomotopicMap h₂ := by
  ext
  simp [nullHomotopicMap]
  abel

@[simp]
lemma nullHomotopicMap_neg (h₁ : ∀ i j, K.X i ⟶ L.X j) :
    nullHomotopicMap (-h₁) = -nullHomotopicMap h₁ := by
  ext
  simp [nullHomotopicMap]
  abel

@[simp]
lemma nullHomotopicMap_sub (h₁ : ∀ i j, K.X i ⟶ L.X j) (h₂ : ∀ i j, K.X i ⟶ L.X j) :
    nullHomotopicMap (h₁ - h₂) = nullHomotopicMap h₁ - nullHomotopicMap h₂ := by
  ext
  simp [nullHomotopicMap]
  abel

end

end Homotopy

namespace ChainComplex

variable {K L : ChainComplex C ℕ} (h : ∀ i j, K.X i ⟶ L.X j)

@[reassoc]
lemma nullHomotopicMap_f_zero :
    (Homotopy.nullHomotopicMap h).f 0 = h 0 1 ≫ L.d 1 0 :=
  Homotopy.nullHomotopicMap_f_of_not_rel_left (by simp) (by simp) _

lemma nullHomotopicMap_f_succ (n : ℕ) :
    (Homotopy.nullHomotopicMap h).f (n + 1) =
        K.d (n + 1) n ≫ h n (n + 1) + h (n + 1) (n + 2) ≫ L.d (n + 2) (n + 1) :=
  Homotopy.nullHomotopicMap_f (by simp) (by simp) _

end ChainComplex
