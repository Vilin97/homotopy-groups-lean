/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.FiniteOrderedComplex

/-!
# A finite cup-square certificate for the nine-vertex projective plane

This file records the 36 facets of the classical nine-vertex triangulation of the complex
projective plane and verifies its decisive mod-two cohomology calculation.  The facet list is the
one in Madahar--Sarkaria, *A Minimal Triangulation of the Hopf Map and its Application*.

With the vertex order `1 < 2 < 3 < 4 < 5 < A < B < C < D`, an explicit degree-two cocycle
evaluates to one on the four-triangle projective-line cycle.  Its Alexander--Whitney square
evaluates to one on the sum of all 36 four-simplices.  The file also verifies that this sum is a
mod-two cycle.  Finite Stokes then proves both the cocycle and its square are not coboundaries.

This is the finite combinatorial certificate needed for the remaining comparison between the
triangulation, geometric `CP²`, and the suspended-Hopf `Sq²` calculation.
-/

namespace Submission

namespace ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The ordered vertex type, displayed in the source as `1,2,3,4,5,A,B,C,D`. -/
abbrev Vertex := Fin 9

/-- The 36 four-dimensional facets of the nine-vertex triangulation of `CP²`.

In the source labels, the six rows are:
```
12ABC 45ACD 12345 13BCD 34ABD 235BD
23ABC 45BCD 1234D 35BCD 134BD 23ABD
31ABC 45ABD 1235D 14BCD 234AD 235BC
1345A 125AB 15ACD 135AC 145AB 125AD
1245B 12ACD 345AC 25ABD 135CD 134AB
2345C 124BC 24ACD 245BC 124CD 234AC
```
-/
def facets : Finset (Finset Vertex) :=
  { {0, 1, 5, 6, 7}, {3, 4, 5, 7, 8}, {0, 1, 2, 3, 4},
    {0, 2, 6, 7, 8}, {2, 3, 5, 6, 8}, {1, 2, 4, 6, 8},
    {1, 2, 5, 6, 7}, {3, 4, 6, 7, 8}, {0, 1, 2, 3, 8},
    {2, 4, 6, 7, 8}, {0, 2, 3, 6, 8}, {1, 2, 5, 6, 8},
    {0, 2, 5, 6, 7}, {3, 4, 5, 6, 8}, {0, 1, 2, 4, 8},
    {0, 3, 6, 7, 8}, {1, 2, 3, 5, 8}, {1, 2, 4, 6, 7},
    {0, 2, 3, 4, 5}, {0, 1, 4, 5, 6}, {0, 4, 5, 7, 8},
    {0, 2, 4, 5, 7}, {0, 3, 4, 5, 6}, {0, 1, 4, 5, 8},
    {0, 1, 3, 4, 6}, {0, 1, 5, 7, 8}, {2, 3, 4, 5, 7},
    {1, 4, 5, 6, 8}, {0, 2, 4, 7, 8}, {0, 2, 3, 5, 6},
    {1, 2, 3, 4, 7}, {0, 1, 3, 6, 7}, {1, 3, 5, 7, 8},
    {1, 3, 4, 6, 7}, {0, 1, 3, 7, 8}, {1, 2, 3, 5, 7} }

/-- The triangulation has the expected 36 distinct top-dimensional simplices. -/
theorem facets_card : facets.card = 36 := by decide

/-- Every listed facet has five vertices. -/
theorem facets_pure : ∀ σ ∈ facets, σ.card = 5 := by
  intro σ hσ
  exact (by decide : ∀ τ : ↥facets, τ.1.card = 5) ⟨σ, hσ⟩

/-- The verified `f`-vector of the triangulation is `(9, 36, 84, 90, 36)`. -/
theorem f_vector :
    ((facesOfCard facets 1).card, (facesOfCard facets 2).card,
      (facesOfCard facets 3).card, (facesOfCard facets 4).card,
      (facesOfCard facets 5).card) =
        (9, 36, 84, 90, 36) := by decide

/-- Every tetrahedron belongs to exactly two facets, as expected for the top-dimensional
incidence relation of this closed triangulated four-manifold. -/
theorem tetrahedron_incidence_two :
    ∀ τ ∈ facesOfCard facets 4,
      (facets.filter fun σ ↦ τ ∈ σ.powersetCard 4).card = 2 := by
  intro τ hτ
  have hcheck :
      (facesOfCard facets 4).filter
          (fun ρ ↦ (facets.filter fun σ ↦ ρ ∈ σ.powersetCard 4).card ≠ 2) = ∅ := by
    decide
  have hn : τ ∉ (facesOfCard facets 4).filter
      (fun ρ ↦ (facets.filter fun σ ↦ ρ ∈ σ.powersetCard 4).card ≠ 2) := by
    rw [hcheck]
    simp
  simpa only [Finset.mem_filter, hτ, true_and, not_not] using hn

/-- Support of the explicit degree-two cocycle. -/
def degreeTwoSupport : Finset (Finset Vertex) :=
  { {0, 1, 6}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5},
    {0, 4, 6}, {0, 5, 6}, {1, 2, 7}, {1, 3, 4},
    {1, 3, 6}, {1, 4, 7}, {1, 6, 7}, {2, 3, 4},
    {2, 3, 7}, {2, 4, 5}, {2, 5, 7}, {5, 6, 7} }

/-- The explicit mod-two degree-two cochain. -/
def degreeTwoCocycle : FiniteOrderedComplex.Cochain Vertex :=
  fun σ ↦ if σ ∈ degreeTwoSupport then 1 else 0

/-- Direct finite verification that the displayed cochain is a cocycle. -/
theorem degreeTwoCocycle_isCocycle :
    IsCocycle facets 2 degreeTwoCocycle := by
  change (facesOfCard facets 4).filter
      (fun σ ↦ coboundary 3 degreeTwoCocycle σ ≠ 0) = ∅
  decide

/-- A four-triangle cycle representing the projective line.  It is the boundary of the abstract
tetrahedron `123A`, although that tetrahedron is not itself a simplex of the triangulation. -/
def projectiveLineCycle : Finset (Finset Vertex) :=
  { {0, 1, 2}, {0, 1, 5}, {0, 2, 5}, {1, 2, 5} }

/-- Every triangle in the displayed projective-line cycle belongs to the triangulation. -/
theorem projectiveLineCycle_faces :
    projectiveLineCycle ⊆ facesOfCard facets 3 := by decide

/-- The four projective-line triangles form a mod-two two-cycle. -/
theorem projectiveLineCycle_isCycle :
    IsCycle 2 projectiveLineCycle := by
  change (facesOfCard projectiveLineCycle 2).filter
      (fun τ ↦ boundaryCoefficient 2 projectiveLineCycle τ ≠ 0) = ∅
  decide

/-- The degree-two cocycle evaluates nontrivially on the projective-line cycle. -/
theorem degreeTwoCocycle_evaluate_projectiveLineCycle :
    evaluate projectiveLineCycle degreeTwoCocycle = 1 := by decide

/-- Consequently the explicit degree-two cocycle is not a coboundary. -/
theorem degreeTwoCocycle_not_isCoboundaryOn :
    ¬ IsCoboundaryOn facets 2 degreeTwoCocycle := by
  apply not_isCoboundaryOn_of_cycle_evaluation_ne_zero
    projectiveLineCycle_faces projectiveLineCycle_isCycle
  rw [degreeTwoCocycle_evaluate_projectiveLineCycle]
  decide

/-- The Alexander--Whitney square of the explicit degree-two cocycle. -/
def degreeTwoCupSquare : FiniteOrderedComplex.Cochain Vertex :=
  cup 2 degreeTwoCocycle degreeTwoCocycle

/-- Exactly one facet contributes to the displayed cup-square evaluation.  In the source labels
it is `13ABC`. -/
theorem degreeTwoCupSquare_contributors :
    facets.filter (fun σ ↦ degreeTwoCupSquare σ = 1) =
      { {0, 2, 5, 6, 7} } := by decide

/-- There are no simplices above dimension four, so the cup square is a degree-four cocycle. -/
theorem degreeTwoCupSquare_isCocycle :
    IsCocycle facets 4 degreeTwoCupSquare := by
  change (facesOfCard facets 6).filter
      (fun σ ↦ coboundary 5 degreeTwoCupSquare σ ≠ 0) = ∅
  decide

/-- The sum of all 36 facets is a mod-two four-cycle. -/
theorem facets_isCycle : IsCycle 4 facets := by
  change (facesOfCard facets 4).filter
      (fun τ ↦ boundaryCoefficient 4 facets τ ≠ 0) = ∅
  decide

/-- Every top-dimensional facet is among the generated five-vertex faces. -/
theorem facets_faces : facets ⊆ facesOfCard facets 5 := by decide

/-- The Alexander--Whitney square evaluates to one on the fundamental mod-two cycle. -/
theorem degreeTwoCupSquare_evaluate_facets :
    evaluate facets degreeTwoCupSquare = 1 := by decide

/-- The cup square represents a nonzero degree-four simplicial cohomology class. -/
theorem degreeTwoCupSquare_not_isCoboundaryOn :
    ¬ IsCoboundaryOn facets 4 degreeTwoCupSquare := by
  apply not_isCoboundaryOn_of_cycle_evaluation_ne_zero facets_faces facets_isCycle
  rw [degreeTwoCupSquare_evaluate_facets]
  decide

/-- Bundled statement of the finite cup-square certificate. -/
theorem cupSquare_certificate :
    IsCocycle facets 2 degreeTwoCocycle ∧
      ¬ IsCoboundaryOn facets 2 degreeTwoCocycle ∧
      IsCycle 4 facets ∧
      evaluate facets (cup 2 degreeTwoCocycle degreeTwoCocycle) = 1 ∧
      ¬ IsCoboundaryOn facets 4 (cup 2 degreeTwoCocycle degreeTwoCocycle) := by
  exact ⟨degreeTwoCocycle_isCocycle, degreeTwoCocycle_not_isCoboundaryOn,
    facets_isCycle, degreeTwoCupSquare_evaluate_facets,
    degreeTwoCupSquare_not_isCoboundaryOn⟩

end ComplexProjectivePlaneTriangulation

end Submission
