/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.FiniteOrderedComplexReindex
import Submission.SSetBoundaryRealization

/-!
# Realizations of certified bistellar-sphere endpoints

An `IsBistellarSphere` certificate supplies a valid bistellar-move sequence whose computed
endpoint is a finite simplex boundary.  Reindexing identifies the endpoint simplicial set with
Mathlib's standard simplicial boundary, while `Submission.SSetBoundaryRealization` identifies the
realization of that boundary with the exact metric sphere used by the homotopy-group library.

This theorem concerns the computed endpoint.  A homeomorphism from the original complex requires
the separate realization-invariance theorem for each valid bistellar move.
-/

noncomputable section

namespace Submission.FiniteOrderedComplex

open CategoryTheory Simplicial

variable {V : Type} [LinearOrder V]

/-- Every combinatorial bistellar-sphere certificate has a valid move sequence whose computed
endpoint realization is homeomorphic to the exact metric sphere of the certified dimension. -/
theorem IsBistellarSphere.exists_endpointRealizationHomeomorphSphere
    {facets : Finset (Finset V)} {dimension : ℕ}
    (h : IsBistellarSphere facets dimension) :
    ∃ moves : List (BistellarMoveData V),
      IsValidBistellarMoveSequence facets dimension moves ∧
        Nonempty
          (SSet.toTop.obj (orderedSSet (applyBistellarMoves facets moves)) ≃ₜ
            SphereSpace dimension) := by
  rcases h.exists_endpointRealizationIso with ⟨moves, hvalid, ⟨e⟩⟩
  exact ⟨moves, hvalid,
    ⟨(TopCat.homeoOfIso e).trans (boundaryRealizationHomeomorphSphere dimension)⟩⟩

end Submission.FiniteOrderedComplex
