/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.BistellarMoveDecomposition

/-!
# Realizations of certified bistellar-sphere endpoints

An `IsBistellarSphere` certificate supplies a valid bistellar-move sequence whose computed
endpoint is a finite simplex boundary.  Reindexing identifies the endpoint simplicial set with
Mathlib's standard simplicial boundary, while `Submission.SSetBoundaryRealization` identifies the
realization of that boundary with the exact metric sphere used by the homotopy-group library.

Realization invariance for one valid move iterates over the certified sequence.  Consequently the
original finite ordered complex—not only its computed endpoint—has realization homeomorphic to
the standard simplicial boundary and to the exact metric sphere.

## Main results

* `bistellarMoveSequenceRealizationIso`: realization invariance along any valid move sequence;
* `IsBistellarSphere.nonempty_realizationIsoBoundary`: the certified complex realizes as the
  standard simplicial sphere;
* `IsBistellarSphere.nonempty_realizationHomeomorphSphere`: the certified complex realizes as the
  exact metric sphere.
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

/-- A valid sequence of bistellar replacements preserves the realization homeomorphism type. -/
noncomputable def bistellarMoveSequenceRealizationIso
    (facets : Finset (Finset V)) (dimension : ℕ)
    (moves : List (BistellarMoveData V))
    (h : IsValidBistellarMoveSequence facets dimension moves) :
    SSet.toTop.obj (orderedSSet facets) ≅
      SSet.toTop.obj (orderedSSet (applyBistellarMoves facets moves)) := by
  induction moves generalizing facets with
  | nil => exact Iso.refl _
  | cons move moves ih =>
      exact bistellarMoveRealizationIso h.1 ≪≫ ih _ h.2

/-- A combinatorial bistellar-sphere certificate realizes as the standard simplicial sphere. -/
theorem IsBistellarSphere.nonempty_realizationIsoBoundary
    {facets : Finset (Finset V)} {dimension : ℕ}
    (h : IsBistellarSphere facets dimension) :
    Nonempty (SSet.toTop.obj (orderedSSet facets) ≅
      SSet.toTop.obj (SSet.boundary (dimension + 1) : SSet)) := by
  rcases h.exists_endpointSSetIso with ⟨moves, hvalid, ⟨endpointIso⟩⟩
  exact ⟨bistellarMoveSequenceRealizationIso facets dimension moves hvalid ≪≫
    SSet.toTop.mapIso endpointIso⟩

/-- A combinatorial bistellar `dimension`-sphere has realization homeomorphic to the exact metric
`dimension`-sphere. -/
theorem IsBistellarSphere.nonempty_realizationHomeomorphSphere
    {facets : Finset (Finset V)} {dimension : ℕ}
    (h : IsBistellarSphere facets dimension) :
    Nonempty (SSet.toTop.obj (orderedSSet facets) ≃ₜ SphereSpace dimension) := by
  rcases h.nonempty_realizationIsoBoundary with ⟨e⟩
  exact ⟨(TopCat.homeoOfIso e).trans
    (boundaryRealizationHomeomorphSphere dimension)⟩

end Submission.FiniteOrderedComplex
