/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Cohomology.MayerVietoris
import Submission.Homology.MayerVietorisIso

/-!
# Adjoint Mayer--Vietoris suspension isomorphisms

When the two pieces of a cover are contractible, the homological and cohomological connecting
maps are isomorphisms in positive degrees.  This file records that these suspension isomorphisms
remain adjoint under the evaluation pairing.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

variable {X : TopCat.{0}} (A B : Set X) (R : Type) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- The homological and cohomological Mayer--Vietoris suspension isomorphisms for a cover by
contractible pieces are adjoint under evaluation. -/
theorem mv_deltaIso_adjoint_of_contractible
    (h : interior A ∪ interior B = Set.univ) (n : ℕ)
    [ContractibleSpace A] [ContractibleSpace B]
    (Φ : (homDual (Csing (TopCat.of (A ∩ B : Set X)))
      (AddCommGrpCat.of R)).homology (n + 1))
    (z : Hgrp (n + 2) X) :
    ev (Csing X) (AddCommGrpCat.of R) (n + 2)
        ((mvCohδIso_of_contractible A B R h n).hom Φ) z =
      ev (Csing (TopCat.of (A ∩ B : Set X))) (AddCommGrpCat.of R) (n + 1) Φ
        ((mvδIso_of_contractible A B h n).hom z) := by
  exact mv_delta_adjoint A B R h (n + 1) Φ z

end Submission
