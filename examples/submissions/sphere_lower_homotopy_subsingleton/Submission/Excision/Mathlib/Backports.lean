/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
-- Vendored from https://github.com/leanprover-community/mathlib4 (Apache 2.0), commit
-- 1c37b91f964cdf0470eb55e86478ca63c20f3899.
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty

/-!
# Backported Mathlib declarations

This file contains declarations that were added to Mathlib after the revision pinned by this
project, and that are needed by the vendored `excision` library. They are copied verbatim from
`Mathlib/CategoryTheory/Limits/FunctorCategory/Shapes/Kernels.lean` and
`Mathlib/AlgebraicTopology/SimplicialSet/Homology/Basic.lean` at the newer revision,
except that the isomorphisms `parallelPair.ext (Iso.refl _) (Iso.refl _)` are replaced by
`diagramIsoParallelPair`, which avoids a definitional-unfolding issue at the older revision.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {J C : Type*} [Category* J] [Category* C] [HasZeroMorphisms C]
  {F₁ F₂ : J ⥤ C} (f : F₁ ⟶ F₂)

/-- A natural transformation of functors has a kernel as soon as all its components do. -/
lemma hasKernel_of_hasKernel_app [∀ j, HasKernel (f.app j)] : HasKernel f :=
  have (j : J) : HasLimit ((parallelPair f 0).flip.obj j) :=
    hasLimit_of_iso (F := parallelPair (f.app j) 0)
      (diagramIsoParallelPair ((parallelPair f 0).flip.obj j)).symm
  functorCategoryHasLimit _

/-- A natural transformation of functors has a cokernel as soon as all its components do. -/
lemma hasCokernel_of_hasCokernel_app [∀ j, HasCokernel (f.app j)] : HasCokernel f :=
  have (j : J) : HasColimit ((parallelPair f 0).flip.obj j) :=
    hasColimit_of_iso (F := parallelPair (f.app j) 0)
      (diagramIsoParallelPair ((parallelPair f 0).flip.obj j))
  functorCategoryHasColimit _

/-- Evaluation preserves the kernel of a natural transformation whose components have kernels. -/
lemma evaluation_preservesKernel_of_hasKernel_app [∀ j, HasKernel (f.app j)] (j : J) :
    PreservesLimit (parallelPair f 0) ((evaluation _ _).obj j) :=
  have (j : J) : HasLimit ((parallelPair f 0).flip.obj j) :=
    hasLimit_of_iso (F := parallelPair (f.app j) 0)
      (diagramIsoParallelPair ((parallelPair f 0).flip.obj j)).symm
  preservesLimit_of_preserves_limit_cone
    (combinedIsLimit (F := parallelPair f 0)
      (fun j ↦ getLimitCone ((parallelPair f 0).flip.obj j)))
    (limit.isLimit _)

/-- Evaluation preserves the cokernel of a natural transformation whose components
have cokernels. -/
lemma evaluation_preservesCokernel_of_hasCokernel_app [∀ j, HasCokernel (f.app j)] (j : J) :
    PreservesColimit (parallelPair f 0) ((evaluation _ _).obj j) :=
  have (j : J) : HasColimit ((parallelPair f 0).flip.obj j) :=
    hasColimit_of_iso (F := parallelPair (f.app j) 0)
      (diagramIsoParallelPair ((parallelPair f 0).flip.obj j))
  preservesColimit_of_preserves_colimit_cocone
    (combinedIsColimit (F := parallelPair f 0)
      (fun j ↦ getColimitCocone ((parallelPair f 0).flip.obj j)))
    (colimit.isColimit _)

end CategoryTheory.Limits

open CategoryTheory Limits Simplicial

namespace SSet

variable {C : Type*} [Category* C] [HasCoproducts C] [Preadditive C]

/-- The chain complex of a simplicial set with no simplices is zero. -/
lemma isZero_chainComplex (X : SSet) (R : C) [X.HasDimensionLT 0] :
    IsZero (X.chainComplex R) := by
  rw [IsZero.iff_id_eq_zero]
  ext n x
  exact ((X.notNonempty_iff_hasDimensionLT_zero.mpr inferInstance)
    ⟨X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op x⟩).elim

end SSet
