/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.SimplicialSplitting
import Submission.Homology.Point

/-!
# Degree zero singular homology and point classes

For a `0`-simplex `y` of a simplicial set `Y` there is a class `ptClass Y y : ℤ ⟶ H₀(Y)`.  Mathlib
records that composing it with the augmentation gives the identity; consequently, over a
path-connected space (where the augmentation is an isomorphism) the point class is an isomorphism.
Point classes are natural, so **any** map between path-connected spaces induces an isomorphism on
`H₀`.

## Main results

* `ptClass` and `ptClass_naturality`;
* `isIso_ptClass` — the point class of a path-connected space is an isomorphism;
* `isIso_HgrpMap_zero` — a map between path-connected spaces is an `H₀`-isomorphism.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

noncomputable section

namespace Submission

/-- The class in `H₀` of a `0`-simplex. -/
def ptClass (Y : SSet.{0}) (y : Y _⦋0⦌) : AddCommGrpCat.of ℤ ⟶ (CsingSSet Y).homology 0 :=
  (CsingSSet Y).liftCycles (Y.ιChainComplex y) 0 (by simp) (by simp) ≫
    (CsingSSet Y).homologyπ 0

/-- The class in `H₀(X)` of a `0`-simplex of a topological space. -/
def ptClassTop (X : TopCat.{0}) (y : (TopCat.toSSet.obj X) _⦋0⦌) :
    AddCommGrpCat.of ℤ ⟶ Hgrp 0 X := ptClass (TopCat.toSSet.obj X) y

/-- The point class is a section of the augmentation `H₀(X) ⟶ ℤ`. -/
theorem ptClassTop_comp_aug (X : TopCat.{0}) (y : (TopCat.toSSet.obj X) _⦋0⦌) :
    ptClassTop X y ≫ hgrpAug X = 𝟙 (AddCommGrpCat.of ℤ) := by
  show ptClass (TopCat.toSSet.obj X) y ≫ hgrpAug X = 𝟙 (AddCommGrpCat.of ℤ)
  rw [ptClass, Category.assoc]
  exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε _ _ y

/-- Point classes are natural. -/
theorem ptClass_naturality {Y Z : SSet.{0}} (f : Y ⟶ Z) (y : Y _⦋0⦌) :
    ptClass Y y ≫
        HomologicalComplex.homologyMap (SSet.chainComplexMap f (AddCommGrpCat.of ℤ)) 0 =
      ptClass Z (f.app _ y) := by
  rw [ptClass, ptClass, Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  congr 2
  simp

/-- Point classes are natural, in `TopCat`. -/
theorem ptClassTop_naturality {Y Z : TopCat.{0}} (f : Y ⟶ Z)
    (y : (TopCat.toSSet.obj Y) _⦋0⦌) :
    ptClassTop Y y ≫ HgrpMap 0 f = ptClassTop Z ((TopCat.toSSet.map f).app _ y) :=
  ptClass_naturality (TopCat.toSSet.map f) y

/-- Over a path-connected space the point class is an isomorphism. -/
instance isIso_ptClassTop (X : TopCat.{0}) [PathConnectedSpace X]
    (y : (TopCat.toSSet.obj X) _⦋0⦌) : IsIso (ptClassTop X y) := by
  have h : IsIso (ptClassTop X y ≫ hgrpAug X) := by
    rw [ptClassTop_comp_aug]; infer_instance
  exact IsIso.of_isIso_comp_right (ptClassTop X y) (hgrpAug X)

/-- **A map between path-connected spaces is an isomorphism on `H₀`.** -/
theorem isIso_HgrpMap_zero {Y Z : TopCat.{0}} [PathConnectedSpace Y] [PathConnectedSpace Z]
    (f : Y ⟶ Z) : IsIso (HgrpMap 0 f) := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  set s : (TopCat.toSSet.obj Y) _⦋0⦌ := Y.toSSetObj₀Equiv.symm y with hs
  have h3 : IsIso (ptClassTop Y s ≫ HgrpMap 0 f) := by
    rw [ptClassTop_naturality]; infer_instance
  exact IsIso.of_isIso_comp_left (ptClassTop Y s) (HgrpMap 0 f)

end Submission
