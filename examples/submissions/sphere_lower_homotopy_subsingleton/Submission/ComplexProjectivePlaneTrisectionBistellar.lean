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

/-- The base at apex `0` is a bistellar three-sphere in the executable combinatorial sense. -/
theorem trisectionPieceZeroBase_isBistellarThreeSphere :
    IsBistellarSphere (trisectionPieceBaseFacets 0) 3 :=
  ⟨trisectionPieceZeroBaseBistellarMoves, {3, 6, 8, 10, 12}, by decide,
    trisectionPieceZeroBaseBistellarMoves_valid,
    trisectionPieceZeroBase_bistellar_result⟩

/-- Rotate both cores of one bistellar move. -/
def rotateBistellarMoveData (move : BistellarMoveData TrisectionVertex) :
    BistellarMoveData TrisectionVertex :=
  ⟨move.oldCore.image trisectionRotationFun,
    move.newCore.image trisectionRotationFun⟩

/-- The once-rotated reduction sequence for the base at apex `5`. -/
def trisectionPieceFiveBaseBistellarMoves : List (BistellarMoveData TrisectionVertex) :=
  trisectionPieceZeroBaseBistellarMoves.map rotateBistellarMoveData

/-- The twice-rotated reduction sequence for the base at apex `4`. -/
def trisectionPieceFourBaseBistellarMoves : List (BistellarMoveData TrisectionVertex) :=
  trisectionPieceFiveBaseBistellarMoves.map rotateBistellarMoveData

/-- The once-rotated sequence is valid on the base at apex `5`. -/
theorem trisectionPieceFiveBaseBistellarMoves_valid :
    IsValidBistellarMoveSequence (trisectionPieceBaseFacets 5) 3
      trisectionPieceFiveBaseBistellarMoves := by decide

/-- The once-rotated sequence ends at an explicit four-simplex boundary. -/
theorem trisectionPieceFiveBase_bistellar_result :
    applyBistellarMoves (trisectionPieceBaseFacets 5)
        trisectionPieceFiveBaseBistellarMoves =
      simplexBoundaryFacets {1, 2, 8, 9, 12} := by decide

/-- The base at apex `5` is a bistellar three-sphere. -/
theorem trisectionPieceFiveBase_isBistellarThreeSphere :
    IsBistellarSphere (trisectionPieceBaseFacets 5) 3 :=
  ⟨trisectionPieceFiveBaseBistellarMoves, {1, 2, 8, 9, 12}, by decide,
    trisectionPieceFiveBaseBistellarMoves_valid,
    trisectionPieceFiveBase_bistellar_result⟩

/-- The twice-rotated sequence is valid on the base at apex `4`. -/
theorem trisectionPieceFourBaseBistellarMoves_valid :
    IsValidBistellarMoveSequence (trisectionPieceBaseFacets 4) 3
      trisectionPieceFourBaseBistellarMoves := by decide

/-- The twice-rotated sequence ends at an explicit four-simplex boundary. -/
theorem trisectionPieceFourBase_bistellar_result :
    applyBistellarMoves (trisectionPieceBaseFacets 4)
        trisectionPieceFourBaseBistellarMoves =
      simplexBoundaryFacets {2, 6, 7, 11, 12} := by decide

/-- The base at apex `4` is a bistellar three-sphere. -/
theorem trisectionPieceFourBase_isBistellarThreeSphere :
    IsBistellarSphere (trisectionPieceBaseFacets 4) 3 :=
  ⟨trisectionPieceFourBaseBistellarMoves, {2, 6, 7, 11, 12}, by decide,
    trisectionPieceFourBaseBistellarMoves_valid,
    trisectionPieceFourBase_bistellar_result⟩

/-- All three trisection-piece bases are certified bistellar three-spheres. -/
theorem trisectionPieceBases_areBistellarThreeSpheres :
    IsBistellarSphere (trisectionPieceBaseFacets 0) 3 ∧
      IsBistellarSphere (trisectionPieceBaseFacets 5) 3 ∧
      IsBistellarSphere (trisectionPieceBaseFacets 4) 3 :=
  ⟨trisectionPieceZeroBase_isBistellarThreeSphere,
    trisectionPieceFiveBase_isBistellarThreeSphere,
    trisectionPieceFourBase_isBistellarThreeSphere⟩

end ComplexProjectivePlaneTriangulation

end Submission
