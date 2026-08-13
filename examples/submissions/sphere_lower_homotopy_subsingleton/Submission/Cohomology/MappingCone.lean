/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Cohomology.MayerVietoris
import Submission.Homology.MappingCone
import Submission.Homology.HomotopyEquiv

/-!
# Cohomology of a mapping cone in the suspension range

The standard height cover of a mapping cone identifies its overlap with the attaching space and
its lower collar with the target.  When two adjacent cohomology groups of the target vanish,
cohomological Mayer--Vietoris therefore identifies the shifted cohomology of the attaching space
with the next cohomology group of the mapping cone.  This isomorphism is adjoint to the analogous
homological suspension isomorphism.

## Main results

* `mappingConeCohomologySuspensionIso` gives
  `H^(n+1)(A; R) ≅ H^(n+2)(Cone(f); R)` in the vanishing range.
* `mappingConeSuspensionIso_adjoint` proves compatibility with the homological mapping-cone
  suspension under evaluation.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

variable {A X : TopCat.{0}}

/-- The mapping-cone overlap has the cohomology of the attaching space. -/
def mappingConeMiddleCohomologyIso (f : A ⟶ X) [Nonempty A]
    (R : Type) [CommRing R] (n : ℕ) :
    (homDual (Csing A) (AddCommGrpCat.of R)).homology n ≅
      (homDual (Csing (TopCat.of (mappingConeMiddle f)))
        (AddCommGrpCat.of R)).homology n :=
  let e := mappingConeMiddleHomotopyEquiv f
  (homDualHomotopyEquiv
    (csingHomotopyEquivOfHomotopyEquiv
      (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
      e.left_inv.some e.right_inv.some)
    (AddCommGrpCat.of R)).toHomologyIso n

/-- The lower mapping-cone collar has the cohomology of the target. -/
def mappingConeLowerCohomologyIso (f : A ⟶ X) [Nonempty X]
    (R : Type) [CommRing R] (n : ℕ) :
    (homDual (Csing X) (AddCommGrpCat.of R)).homology n ≅
      (homDual (Csing (TopCat.of (mappingConeLower f)))
        (AddCommGrpCat.of R)).homology n :=
  let e := mappingConeLowerHomotopyEquiv f
  (homDualHomotopyEquiv
    (csingHomotopyEquivOfHomotopyEquiv
      (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
      e.left_inv.some e.right_inv.some)
    (AddCommGrpCat.of R)).toHomologyIso n

/-- Cohomology vanishing transfers from the target to the lower mapping-cone collar. -/
theorem isZero_mappingConeLowerCohomology (f : A ⟶ X) [Nonempty X]
    (R : Type) [CommRing R] (n : ℕ)
    (hX : IsZero ((homDual (Csing X) (AddCommGrpCat.of R)).homology n)) :
    IsZero ((homDual (Csing (TopCat.of (mappingConeLower f)))
      (AddCommGrpCat.of R)).homology n) :=
  IsZero.of_iso hX (mappingConeLowerCohomologyIso f R n).symm

/-- The cohomological mapping-cone suspension isomorphism in a range where the two adjacent
cohomology groups of the target vanish. -/
def mappingConeCohomologySuspensionIso (f : A ⟶ X) [Nonempty A] [Nonempty X]
    (R : Type) [CommRing R] (n : ℕ)
    (hX₀ : IsZero ((homDual (Csing X) (AddCommGrpCat.of R)).homology (n + 1)))
    (hX₁ : IsZero ((homDual (Csing X) (AddCommGrpCat.of R)).homology (n + 2))) :
    (homDual (Csing A) (AddCommGrpCat.of R)).homology (n + 1) ≅
      (homDual (Csing (topologicalMappingCone f))
        (AddCommGrpCat.of R)).homology (n + 2) :=
  mappingConeMiddleCohomologyIso f R (n + 1) ≪≫
    (mvCohSC_shortExact (mappingConeUpper f) (mappingConeLower f) R).δIso
      (n + 1) (n + 2) (mvCohRel (n + 1))
      (isZero_mvCohSC_X₂_homology (mappingConeUpper f) (mappingConeLower f) R (n + 1)
        (isZero_dualHomology_of_contractible R (n + 1) (by omega))
        (isZero_mappingConeLowerCohomology f R (n + 1) hX₀))
      (isZero_mvCohSC_X₂_homology (mappingConeUpper f) (mappingConeLower f) R (n + 2)
        (isZero_dualHomology_of_contractible R (n + 2) (by omega))
        (isZero_mappingConeLowerCohomology f R (n + 2) hX₁)) ≪≫
    (mvSmallCohomologyIso (mappingConeUpper f) (mappingConeLower f) R
      (mappingConeCover_interior_union f) (n + 2)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The cohomological and homological mapping-cone suspension isomorphisms are adjoint under
evaluation. -/
theorem mappingConeSuspensionIso_adjoint (f : A ⟶ X) [Nonempty A] [Nonempty X]
    (R : Type) [CommRing R] (n : ℕ)
    (hH₁ : IsZero (Hgrp (n + 2) X)) (hH₀ : IsZero (Hgrp (n + 1) X))
    (hC₀ : IsZero ((homDual (Csing X) (AddCommGrpCat.of R)).homology (n + 1)))
    (hC₁ : IsZero ((homDual (Csing X) (AddCommGrpCat.of R)).homology (n + 2)))
    (Φ : (homDual (Csing A) (AddCommGrpCat.of R)).homology (n + 1))
    (z : Hgrp (n + 2) (topologicalMappingCone f)) :
    ev (Csing (topologicalMappingCone f)) (AddCommGrpCat.of R) (n + 2)
        ((mappingConeCohomologySuspensionIso f R n hC₀ hC₁).hom Φ) z =
      ev (Csing A) (AddCommGrpCat.of R) (n + 1) Φ
        ((mappingConeHomologySuspensionIso f n hH₁ hH₀).hom z) := by
  let e := mappingConeMiddleHomotopyEquiv f
  let g : TopCat.of (mappingConeMiddle f) ⟶ A := TopCat.ofHom e.toFun
  let Φmid := (mappingConeMiddleCohomologyIso f R (n + 1)).hom Φ
  let zmid := mvδ (mappingConeUpper f) (mappingConeLower f)
    (mappingConeCover_interior_union f) (n + 1) z
  have hmv := mv_delta_adjoint (mappingConeUpper f) (mappingConeLower f) R
    (mappingConeCover_interior_union f) (n + 1) Φmid z
  have hnat := ev_naturality_apply
    (K := Csing (TopCat.of (mappingConeMiddle f))) (L := Csing A)
    (G := AddCommGrpCat.of R) (i := n + 1) (CsingMap g) Φ
  have hnat' := ConcreteCategory.congr_hom hnat zmid
  change ev (Csing (TopCat.of (mappingConeMiddle f))) (AddCommGrpCat.of R) (n + 1)
      Φmid zmid = ev (Csing A) (AddCommGrpCat.of R) (n + 1) Φ
        (HgrpMap (n + 1) g zmid) at hnat'
  change ev (Csing (topologicalMappingCone f)) (AddCommGrpCat.of R) (n + 2)
      ((mappingConeCohomologySuspensionIso f R n hC₀ hC₁).hom Φ) z =
    ev (Csing (TopCat.of (mappingConeMiddle f))) (AddCommGrpCat.of R) (n + 1)
      Φmid zmid at hmv
  have hz : HgrpMap (n + 1) g zmid =
      (mappingConeHomologySuspensionIso f n hH₁ hH₀).hom z := by
    rfl
  rw [hz] at hnat'
  exact hmv.trans hnat'

end Submission
