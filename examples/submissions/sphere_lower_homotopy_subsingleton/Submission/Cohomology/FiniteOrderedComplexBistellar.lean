/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.FiniteOrderedComplex

/-!
# Executable bistellar-move certificates

This file defines a finite checker for bistellar moves on pure facet families.  A move with
disjoint nonempty cores `A` and `B` replaces `A * ∂B` by `∂A * B`.  The validity predicate checks
the complete top-dimensional star of `A`, absence of `B`, purity, disjointness, and the dimension
equation.  A recursive checker validates an entire explicit move sequence.

The file records combinatorial data only.  The theorem that geometric realization carries a valid
bistellar move to a PL homeomorphism is a separate future bridge.
-/

namespace Submission

namespace FiniteOrderedComplex

variable {V : Type} [DecidableEq V]

/-- The facets of `A * ∂B` removed by a bistellar move. -/
def bistellarOldFacets (A B : Finset V) : Finset (Finset V) :=
  B.image fun b ↦ A ∪ B.erase b

/-- The facets of `∂A * B` inserted by a bistellar move. -/
def bistellarNewFacets (A B : Finset V) : Finset (Finset V) :=
  A.image fun a ↦ A.erase a ∪ B

/-- Apply the facet replacement underlying a bistellar move. -/
def bistellarMove (facets : Finset (Finset V)) (A B : Finset V) :
    Finset (Finset V) :=
  (facets \ bistellarOldFacets A B) ∪ bistellarNewFacets A B

/-- Executable validity predicate for a bistellar move on a pure `dimension`-complex.  The facets
containing `A` must be exactly `A * ∂B`, while no facet may contain the new core `B`. -/
def IsBistellarMove (facets : Finset (Finset V)) (dimension : ℕ) (A B : Finset V) : Prop :=
  facets.filter (fun σ ↦ σ.card ≠ dimension + 1) = ∅ ∧
    A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
    (A ∪ B).card = dimension + 2 ∧
    facets.filter (fun σ ↦ A ⊆ σ) = bistellarOldFacets A B ∧
    facets.filter (fun σ ↦ B ⊆ σ) = ∅

instance (facets : Finset (Finset V)) (dimension : ℕ) (A B : Finset V) :
    Decidable (IsBistellarMove facets dimension A B) := by
  unfold IsBistellarMove
  infer_instance

/-- The two cores specifying one bistellar facet replacement. -/
structure BistellarMoveData (V : Type) where
  oldCore : Finset V
  newCore : Finset V
deriving DecidableEq

/-- Apply a list of bistellar facet replacements. -/
def applyBistellarMoves (facets : Finset (Finset V)) :
    List (BistellarMoveData V) → Finset (Finset V)
  | [] => facets
  | move :: moves =>
      applyBistellarMoves (bistellarMove facets move.oldCore move.newCore) moves

/-- Recursively validate every move against the facet family produced by its predecessors. -/
def IsValidBistellarMoveSequence (facets : Finset (Finset V)) (dimension : ℕ) :
    List (BistellarMoveData V) → Prop
  | [] => True
  | move :: moves =>
      IsBistellarMove facets dimension move.oldCore move.newCore ∧
        IsValidBistellarMoveSequence
          (bistellarMove facets move.oldCore move.newCore) dimension moves

instance (facets : Finset (Finset V)) (dimension : ℕ)
    (moves : List (BistellarMoveData V)) :
    Decidable (IsValidBistellarMoveSequence facets dimension moves) := by
  induction moves generalizing facets with
  | nil => exact isTrue trivial
  | cons move moves ih =>
      unfold IsValidBistellarMoveSequence
      letI := ih (bistellarMove facets move.oldCore move.newCore)
      infer_instance

/-- Applying a concatenated move list is the same as applying its two parts in sequence. -/
theorem applyBistellarMoves_append (facets : Finset (Finset V))
    (moves₁ moves₂ : List (BistellarMoveData V)) :
    applyBistellarMoves facets (moves₁ ++ moves₂) =
      applyBistellarMoves (applyBistellarMoves facets moves₁) moves₂ := by
  induction moves₁ generalizing facets with
  | nil => rfl
  | cons move moves₁ ih =>
      exact ih (bistellarMove facets move.oldCore move.newCore)

/-- A concatenated move sequence is valid exactly when its first part is valid and its second
part is valid on the facet family produced by the first. -/
theorem isValidBistellarMoveSequence_append_iff
    (facets : Finset (Finset V)) (dimension : ℕ)
    (moves₁ moves₂ : List (BistellarMoveData V)) :
    IsValidBistellarMoveSequence facets dimension (moves₁ ++ moves₂) ↔
      IsValidBistellarMoveSequence facets dimension moves₁ ∧
        IsValidBistellarMoveSequence
          (applyBistellarMoves facets moves₁) dimension moves₂ := by
  induction moves₁ generalizing facets with
  | nil =>
      simp only [List.nil_append, IsValidBistellarMoveSequence,
        applyBistellarMoves, true_and]
  | cons move moves₁ ih =>
      simp only [List.cons_append, IsValidBistellarMoveSequence,
        applyBistellarMoves, ih, and_assoc]

/-- Facets in the boundary of the simplex on a finite vertex set. -/
def simplexBoundaryFacets (vertices : Finset V) : Finset (Finset V) :=
  vertices.image fun v ↦ vertices.erase v

/-- A finite pure complex is a bistellar `dimension`-sphere when an explicit valid move sequence
reduces it to the boundary of a simplex on `dimension + 2` vertices.  This is a combinatorial
certificate; its topological interpretation uses the still-separate PL realization theorem. -/
def IsBistellarSphere (facets : Finset (Finset V)) (dimension : ℕ) : Prop :=
  ∃ (moves : List (BistellarMoveData V)) (vertices : Finset V),
    vertices.card = dimension + 2 ∧
      IsValidBistellarMoveSequence facets dimension moves ∧
      applyBistellarMoves facets moves = simplexBoundaryFacets vertices

end FiniteOrderedComplex

end Submission
