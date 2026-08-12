/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SimplicialIndexShift

/-!
# Simplicial relations at arbitrary face indices

The final-index relation theorem is enough for a single simplicial homotopy simplex.  A coherent
simplicial deformation, however, presents a string of relations at all face indices.  This file
uses the arbitrary-index multiplication theorem to show directly that every one of those
relations preserves the stick-coordinate homotopy class.
-/

open CategoryTheory AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

namespace NormalizedSimplex

/-- The constant normalized simplex represents the identity homotopy class in stick-breaking
coordinates. -/
@[simp]
theorem const_stickHomotopyClass (n : ℕ) (x : X) :
    (const n x).stickHomotopyClass = 1 := by
  rw [stickHomotopyClass, HomotopyGroup.one_def]
  apply congrArg Quotient.mk'
  apply GenLoop.ext
  intro t
  exact const_stickMap_apply n x t

end NormalizedSimplex

variable
  {f g : (Sng (TopCat.of X)).PtSimplex (n + 2)
    (TopCat.toSSetObj₀Equiv.symm x)}

/-- A pointed simplicial relation preserves the stick-coordinate homotopy class at every face
index. -/
theorem stickHomotopyClass_ofPtSimplex_rel_at
    (i : Fin (n + 3)) (r : SSet.PtSimplex.RelStruct f g i) :
    (NormalizedSimplex.ofPtSimplex f).stickHomotopyClass =
      (NormalizedSimplex.ofPtSimplex g).stickHomotopyClass := by
  by_cases hi : i = Fin.last (n + 2)
  · subst i
    exact stickHomotopyClass_ofPtSimplex_rel r
  · obtain ⟨q, rfl⟩ := i.eq_castSucc_of_ne_last hi
    have hmul := stickHomotopyClass_ofPtSimplex_mul_at q
      (SSet.PtSimplex.relStructCastSuccEquivMulStruct r)
    simpa using hmul.symm

end Submission
