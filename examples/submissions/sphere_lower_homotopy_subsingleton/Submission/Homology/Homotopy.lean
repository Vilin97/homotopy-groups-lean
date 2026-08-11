/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.Basic
import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# Homotopy invariance of singular homology

Mathlib proves that homotopic maps induce the same map on singular homology
(`TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`). This file packages the
standard consequences: a homotopy equivalence induces an isomorphism on homology, and the
homology of a contractible space is that of a point.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

/-- Homotopic maps induce the same map on singular homology. -/
theorem HgrpMap_congr {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (n : ℕ) :
    HgrpMap n f = HgrpMap n g :=
  H.congr_homologyMap_singularChainComplexFunctor _ _

/-- A homotopy equivalence induces an isomorphism on singular homology. -/
def hgrpIsoOfHomotopyEquiv {X Y : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    (H₁ : TopCat.Homotopy (f ≫ g) (𝟙 X)) (H₂ : TopCat.Homotopy (g ≫ f) (𝟙 Y)) (n : ℕ) :
    Hgrp n X ≅ Hgrp n Y where
  hom := HgrpMap n f
  inv := HgrpMap n g
  hom_inv_id := by
    rw [← HgrpMap_comp, HgrpMap_congr H₁, HgrpMap_id]
  inv_hom_id := by
    rw [← HgrpMap_comp, HgrpMap_congr H₂, HgrpMap_id]

end Submission
