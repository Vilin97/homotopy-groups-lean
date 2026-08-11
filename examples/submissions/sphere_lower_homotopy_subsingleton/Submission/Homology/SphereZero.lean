/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.LesTools
import Submission.Model.Sphere

/-!
# The homology of the `0`-sphere

`S⁰` is a two-point discrete space, so its singular homology vanishes in positive degrees. This is
the base case of the inductive computation of `H̃_*(Sⁿ)` by Mayer–Vietoris.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

instance instTotallyDisconnectedSphZero : TotallyDisconnectedSpace (Sph 0) :=
  inferInstance

/-- The singular homology of `S⁰` vanishes in positive degrees. -/
theorem isZero_Hgrp_sphZero (n : ℕ) (hn : n ≠ 0) : IsZero (Hgrp n (TopCat.of (Sph 0))) :=
  isZero_Hgrp_of_totallyDisconnected n hn _

/-- The reduced homology of `S⁰` vanishes in positive degrees. -/
theorem isZero_Hred_sphZero (n : ℕ) (x : TopCat.of (Sph 0)) : IsZero (Hred (n + 1) x) := by
  refine isZero_Hrel_of_epi_of_mono (ptIncl x) n ?_ ?_
  · have h₂ : IsZero (Hgrp (n + 1) (TopCat.of (Sph 0))) := isZero_Hgrp_sphZero _ n.succ_ne_zero
    exact ⟨fun {_} g h _ => h₂.eq_of_src g h⟩
  · exact mono_relIota_ptIncl n x

end Submission
