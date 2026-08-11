/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.LesTools
import Submission.Homology.Homotopy
import Mathlib.Topology.Homotopy.Contractible

/-!
# Homology of a contractible space

A contractible space has the homology of a point: the inclusion of a basepoint is a homotopy
equivalence, so it induces isomorphisms on homology, and the reduced homology vanishes.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

variable {X : TopCat.{0}}

/-- In a path-connected space the constant maps at any two points are homotopic. -/
def homotopyConstOfJoined {y x : X} (γ : Path y x) :
    TopCat.Homotopy (toPt X ≫ ptIncl y) (toPt X ≫ ptIncl x) where
  toFun p := γ p.1
  continuous_toFun := γ.continuous.comp continuous_fst
  map_zero_left _ := γ.source
  map_one_left _ := γ.target

/-- For a contractible space, the constant map at any basepoint is homotopic to the identity. -/
theorem nonempty_contractibleHomotopy [ContractibleSpace X] (x : X) :
    Nonempty (TopCat.Homotopy (toPt X ≫ ptIncl x) (𝟙 X)) := by
  obtain ⟨y, hy⟩ := id_nullhomotopic X
  obtain ⟨H⟩ := hy.symm
  obtain ⟨γ⟩ := (inferInstance : PathConnectedSpace X).joined y x
  exact ⟨(homotopyConstOfJoined γ).symm.trans H⟩

/-- The inclusion of a basepoint into a contractible space induces isomorphisms on homology. -/
theorem isIso_relIota_ptIncl_of_contractible [ContractibleSpace X] (x : X) (n : ℕ) :
    IsIso (relIota n (ptIncl x)) := by
  obtain ⟨H⟩ := nonempty_contractibleHomotopy x
  exact ⟨(hgrpIsoOfHomotopyEquiv (ptIncl x) (toPt X)
      (ptIncl_comp_toPt x ▸ TopCat.Homotopy.refl (𝟙 (TopCat.of PUnit.{1}))) H n).inv,
    (hgrpIsoOfHomotopyEquiv (ptIncl x) (toPt X)
      (ptIncl_comp_toPt x ▸ TopCat.Homotopy.refl (𝟙 (TopCat.of PUnit.{1}))) H n).hom_inv_id,
    (hgrpIsoOfHomotopyEquiv (ptIncl x) (toPt X)
      (ptIncl_comp_toPt x ▸ TopCat.Homotopy.refl (𝟙 (TopCat.of PUnit.{1}))) H n).inv_hom_id⟩

/-- The reduced homology of a contractible space vanishes in positive degrees. -/
theorem isZero_Hred_of_contractible [ContractibleSpace X] (x : X) (n : ℕ) :
    IsZero (Hred (n + 1) x) := by
  have h₁ := isIso_relIota_ptIncl_of_contractible x (n + 1)
  have h₂ := isIso_relIota_ptIncl_of_contractible x n
  exact isZero_Hrel_of_epi_of_mono _ n inferInstance inferInstance

/-- The homology of a contractible space vanishes in positive degrees. -/
theorem isZero_Hgrp_of_contractible [ContractibleSpace X] (n : ℕ) :
    IsZero (Hgrp (n + 1) X) := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have h := isIso_relIota_ptIncl_of_contractible x (n + 1)
  have hz : IsZero (Hgrp (n + 1) (TopCat.of PUnit.{1})) := isZero_Hgrp_punit _ n.succ_ne_zero
  exact hz.of_iso (asIso (relIota (n + 1) (ptIncl x))).symm

end Submission
