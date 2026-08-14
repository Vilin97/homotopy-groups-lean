/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisection
import Submission.Cohomology.FiniteOrderedComplexBistellar

/-!
# Bistellar simplification of a projective-plane trisection piece

An explicit sequence of nine `3–2` moves and four `4–1` moves simplifies the 26-tetrahedron base
of the trisection piece at vertex `0` to the boundary of a four-simplex.  Move validity and the final
facet equality are finite kernel-checked certificates.  Their PL-topological interpretation awaits
the general realization-invariance theorem for bistellar moves.
-/

namespace Submission

namespace ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-- Thirteen reducing bistellar moves from the 26-tetrahedron base to a simplex boundary. -/
def trisectionPieceZeroBaseBistellarMoves : List (BistellarMoveData TrisectionVertex) :=
  [⟨{3, 9}, {2, 6, 12}⟩,
    ⟨{2, 9}, {6, 7, 12}⟩,
    ⟨{8, 9}, {1, 7, 12}⟩,
    ⟨{9}, {1, 6, 7, 12}⟩,
    ⟨{7, 10}, {2, 8, 12}⟩,
    ⟨{2, 7}, {6, 8, 12}⟩,
    ⟨{2, 6}, {3, 8, 12}⟩,
    ⟨{1, 2}, {3, 8, 10}⟩,
    ⟨{2}, {3, 8, 10, 12}⟩,
    ⟨{3, 7}, {1, 6, 8}⟩,
    ⟨{7}, {1, 6, 8, 12}⟩,
    ⟨{1, 3}, {6, 8, 10}⟩,
    ⟨{1}, {6, 8, 10, 12}⟩]

/-- Every displayed replacement satisfies the full local bistellar-move predicate at the state
produced by the preceding replacements. -/
theorem trisectionPieceZeroBaseBistellarMoves_valid :
    IsValidBistellarMoveSequence (trisectionPieceBaseFacets 0) 3
      trisectionPieceZeroBaseBistellarMoves := by decide

/-- Every move is strictly reducing: the removed family has more facets than the inserted family. -/
theorem trisectionPieceZeroBaseBistellarMoves_reducing :
    ∀ move ∈ trisectionPieceZeroBaseBistellarMoves,
      move.oldCore.card < move.newCore.card := by decide

/-- The thirteen moves end at exactly the five tetrahedra bounding the four-simplex on the
displayed vertex set. -/
theorem trisectionPieceZeroBase_bistellar_result :
    applyBistellarMoves (trisectionPieceBaseFacets 0)
        trisectionPieceZeroBaseBistellarMoves =
      simplexBoundaryFacets {3, 6, 8, 10, 12} := by decide

/-- The final bistellar facet family has the expected boundary f-vector. -/
theorem trisectionPieceZeroBase_bistellar_result_f_vector :
    let result := applyBistellarMoves (trisectionPieceBaseFacets 0)
      trisectionPieceZeroBaseBistellarMoves
    ((facesOfCard result 1).card, (facesOfCard result 2).card,
      (facesOfCard result 3).card, (facesOfCard result 4).card) = (5, 10, 10, 5) := by decide

end ComplexProjectivePlaneTriangulation

end Submission
