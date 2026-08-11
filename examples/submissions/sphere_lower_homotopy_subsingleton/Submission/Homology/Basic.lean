/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Singular homology with integer coefficients

Mathlib's singular homology is set up in a general preadditive target category. This file fixes
the coefficients to `ℤ` and the target to `AddCommGrpCat`, which is what the rest of the
development uses, and records the basic API in that specialisation.
-/

open CategoryTheory AlgebraicTopology

noncomputable section

namespace Submission

/-- The `n`-th singular homology group of a topological space, with `ℤ` coefficients. -/
abbrev Hgrp (n : ℕ) (X : TopCat.{0}) : AddCommGrpCat.{0} :=
  ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).obj X

/-- Singular homology as a functor `TopCat ⥤ AddCommGrpCat`. -/
abbrev HgrpFunctor (n : ℕ) : TopCat.{0} ⥤ AddCommGrpCat.{0} :=
  (singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)

/-- The map induced on singular homology by a continuous map. -/
abbrev HgrpMap (n : ℕ) {X Y : TopCat.{0}} (f : X ⟶ Y) : Hgrp n X ⟶ Hgrp n Y :=
  (HgrpFunctor n).map f

@[simp]
theorem HgrpMap_id (n : ℕ) (X : TopCat.{0}) : HgrpMap n (𝟙 X) = 𝟙 (Hgrp n X) :=
  (HgrpFunctor n).map_id X

@[simp]
theorem HgrpMap_comp (n : ℕ) {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HgrpMap n (f ≫ g) = HgrpMap n f ≫ HgrpMap n g :=
  (HgrpFunctor n).map_comp f g

/-- Homeomorphic spaces have isomorphic singular homology. -/
def hgrpIsoOfIso (n : ℕ) {X Y : TopCat.{0}} (e : X ≅ Y) : Hgrp n X ≅ Hgrp n Y :=
  (HgrpFunctor n).mapIso e

end Submission
