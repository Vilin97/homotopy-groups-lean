/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.CubeFundamentalClass

/-!
# Boundary compatibility of the relative Hurewicz comparison

The connecting homomorphism sends the fundamental relative class of a cube to the oriented
fundamental class of its boundary.  Naturality of the long exact sequence of a pair therefore
identifies the boundary of the relative Hurewicz class represented by a cubical map with the
ordinary homology class carried by its restriction to the boundary.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-- The oriented fundamental class of the boundary of the `(n+2)`-cube, obtained as the boundary
of the relative fundamental class. -/
noncomputable def cubeBoundaryFundamentalClass (n : ℕ) :
    Hgrp (n + 1) (TopCat.of (∂I^(n + 2))) :=
  (cubePairRelativeBoundaryIso n).hom (cubePairFundamentalClass n)

/-- The chosen boundary class has orientation `1` under the identification with `ℤ`. -/
@[simp]
theorem cubeBoundaryTopHomologyIsoInt_fundamentalClass (n : ℕ) :
    (cubeBoundaryTopHomologyIsoInt n).hom (cubeBoundaryFundamentalClass n) = (1 : ℤ) := by
  exact cubePairTopHomologyIsoInt_fundamentalClass n

/-- The boundary of the relative Hurewicz class represented by `p` is the homology class carried
by the restriction of `p` to the boundary of its source cube. -/
theorem relativeHurewicz_mk_boundary (n : ℕ) {X : Type} [TopologicalSpace X]
    {A : Set X} {a : A} (p : RelGenLoop (n + 2) X A a) :
    relδ (n + 1) (subIncl (Y := TopCat.of X) A) (relativeHurewicz n A a ⟦p⟧) =
      HgrpMap (n + 1) (RelGenLoop.pairMap p).subspaceHom
        (cubeBoundaryFundamentalClass n) := by
  have h := ConcreteCategory.congr_hom
    (relδ_naturality (n + 1)
      (subIncl (Y := TopCat.of (I^Fin (n + 2))) (∂I^(n + 2)))
      (subIncl (Y := TopCat.of X) A)
      (RelGenLoop.pairMap p).subIncl_naturality)
    (cubePairFundamentalClass n)
  exact h.symm

end Submission
