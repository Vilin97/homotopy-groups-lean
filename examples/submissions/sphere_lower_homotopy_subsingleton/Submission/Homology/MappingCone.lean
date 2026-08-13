/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Homology.MayerVietorisIso
import Submission.Topology.MappingConeCover

/-!
# Homology of a mapping cone in the suspension range

The standard height cover of a mapping cone has contractible upper collar, lower collar
homotopy equivalent to the target, and overlap homotopy equivalent to the attaching space.
When two adjacent positive-degree homology groups of the target vanish, Mayer--Vietoris therefore
identifies the next homology group of the mapping cone with the shifted homology of the attaching
space.

## Main results

* `Submission.hgrpMappingConeLowerIso` and `Submission.hgrpMappingConeMiddleIso` identify the
  homology of the two noncontractible pieces of the standard cover;
* `Submission.mappingConeHomologySuspensionIso` gives
  `H_(n+2)(Cone(f)) ≅ H_(n+1)(A)` when `H_(n+1)(X)` and `H_(n+2)(X)` vanish.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

variable {A X : TopCat.{0}}

/-- The lower mapping-cone collar has the homology of the target. -/
def hgrpMappingConeLowerIso (f : A ⟶ X) [Nonempty X] (n : ℕ) :
    Hgrp n (TopCat.of (mappingConeLower f)) ≅ Hgrp n X :=
  let e := mappingConeLowerHomotopyEquiv f
  hgrpIsoOfHomotopyEquiv (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
    e.left_inv.some e.right_inv.some n

/-- The overlap of the standard mapping-cone cover has the homology of the attaching space. -/
def hgrpMappingConeMiddleIso (f : A ⟶ X) [Nonempty A] (n : ℕ) :
    Hgrp n (TopCat.of (mappingConeMiddle f)) ≅ Hgrp n A :=
  let e := mappingConeMiddleHomotopyEquiv f
  hgrpIsoOfHomotopyEquiv (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
    e.left_inv.some e.right_inv.some n

/-- Homology vanishing transfers from the target to the lower mapping-cone collar. -/
theorem isZero_Hgrp_mappingConeLower (f : A ⟶ X) [Nonempty X] (n : ℕ)
    (hX : IsZero (Hgrp n X)) :
    IsZero (Hgrp n (TopCat.of (mappingConeLower f))) :=
  IsZero.of_iso hX (hgrpMappingConeLowerIso f n)

/-- The interiors of the two standard mapping-cone collars cover the mapping cone. -/
theorem mappingConeCover_interior_union (f : A ⟶ X) :
    interior (mappingConeUpper f) ∪ interior (mappingConeLower f) = Set.univ := by
  rw [(isOpen_mappingConeUpper f).interior_eq,
    (isOpen_mappingConeLower f).interior_eq, mappingConeUpper_union_lower]

/-- In the range where two adjacent positive-degree homology groups of the target vanish, the
mapping-cone connecting morphism is the suspension isomorphism
`H_(n+2)(Cone(f)) ≅ H_(n+1)(A)`. -/
def mappingConeHomologySuspensionIso (f : A ⟶ X) [Nonempty A] [Nonempty X] (n : ℕ)
    (hX₁ : IsZero (Hgrp (n + 2) X))
    (hX₀ : IsZero (Hgrp (n + 1) X)) :
    Hgrp (n + 2) (topologicalMappingCone f) ≅ Hgrp (n + 1) A :=
  mvδIso (mappingConeUpper f) (mappingConeLower f)
      (mappingConeCover_interior_union f) (n + 1)
      (isZero_Hgrp_of_contractible (X := TopCat.of (mappingConeUpper f)) (n + 1))
      (isZero_Hgrp_mappingConeLower f (n + 2) hX₁)
      (isZero_Hgrp_of_contractible (X := TopCat.of (mappingConeUpper f)) n)
      (isZero_Hgrp_mappingConeLower f (n + 1) hX₀) ≪≫
    hgrpMappingConeMiddleIso f (n + 1)

end Submission
