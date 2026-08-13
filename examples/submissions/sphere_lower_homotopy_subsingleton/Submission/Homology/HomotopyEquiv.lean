/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Homology.Homotopy
import Submission.Homology.Pair

/-!
# Homotopy equivalences on singular chain complexes

A homotopy equivalence of spaces induces a chain-homotopy equivalence of their integral singular
chain complexes.  This is the chain-level form of homotopy invariance needed by contravariant
constructions such as relative cohomology.
-/

open CategoryTheory AlgebraicTopology

noncomputable section

namespace Submission

/-- A homotopy equivalence of spaces induces a chain-homotopy equivalence on singular chains. -/
def csingHomotopyEquivOfHomotopyEquiv {X Y : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ X)
    (H₁ : TopCat.Homotopy (f ≫ g) (𝟙 X))
    (H₂ : TopCat.Homotopy (g ≫ f) (𝟙 Y)) :
    HomotopyEquiv (Csing X) (Csing Y) where
  hom := CsingMap f
  inv := CsingMap g
  homotopyHomInvId := by
    let H := H₁.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)
    change Homotopy (CsingMap (f ≫ g)) (CsingMap (𝟙 X)) at H
    rw [CsingMap_comp, CsingMap_id] at H
    exact H
  homotopyInvHomId := by
    let H := H₂.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)
    change Homotopy (CsingMap (g ≫ f)) (CsingMap (𝟙 Y)) at H
    rw [CsingMap_comp, CsingMap_id] at H
    exact H

end Submission
