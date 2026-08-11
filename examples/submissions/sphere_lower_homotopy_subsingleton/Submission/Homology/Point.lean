/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.Basic

/-!
# Homology of a point, and `H₀` of a path-connected space

Two immediate consequences of what Mathlib already knows about singular homology:

* the homology of a totally disconnected space (in particular a point) vanishes in positive
  degrees;
* for a path-connected space the augmentation `H₀(X) ⟶ ℤ` is an isomorphism.
-/

open CategoryTheory AlgebraicTopology Limits

noncomputable section

namespace Submission

/-- The singular homology of a totally disconnected space vanishes in positive degrees. -/
theorem isZero_Hgrp_of_totallyDisconnected (n : ℕ) (hn : n ≠ 0) (X : TopCat.{0})
    [TotallyDisconnectedSpace X] : IsZero (Hgrp n X) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ _ _ _ hn

/-- The singular homology of a point vanishes in positive degrees. -/
theorem isZero_Hgrp_punit (n : ℕ) (hn : n ≠ 0) : IsZero (Hgrp n (TopCat.of PUnit.{1})) :=
  isZero_Hgrp_of_totallyDisconnected n hn _

/-- The augmentation `H₀(X) ⟶ ℤ`. -/
abbrev hgrpAug (X : TopCat.{0}) : Hgrp 0 X ⟶ AddCommGrpCat.of ℤ :=
  X.singularHomology₀ε (AddCommGrpCat.of ℤ)

/-- For a path-connected space the augmentation `H₀(X) ⟶ ℤ` is an isomorphism. -/
instance isIso_hgrpAug (X : TopCat.{0}) [PathConnectedSpace X] : IsIso (hgrpAug X) :=
  inferInstance

/-- `H₀` of a path-connected space is `ℤ`. -/
def hgrpZeroIso (X : TopCat.{0}) [PathConnectedSpace X] : Hgrp 0 X ≅ AddCommGrpCat.of ℤ :=
  asIso (hgrpAug X)

end Submission
