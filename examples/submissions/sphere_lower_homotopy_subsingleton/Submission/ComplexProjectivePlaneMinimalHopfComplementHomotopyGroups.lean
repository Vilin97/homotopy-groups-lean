/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfComplementCollapse
import Submission.Lean4TwentyResults

/-!
# Homotopy groups of the complementary finite Hopf piece

The explicit seventy-two-collapse certificate identifies the complementary preimage with the
homotopy type of the exact metric circle.  This file records the resulting homotopy-group
calculation at every basepoint: the fundamental group is infinite cyclic and every group above
degree one vanishes.
-/

noncomputable section

open Simplicial
open scoped Topology Topology.Homotopy

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The fundamental group of the complementary finite Hopf piece is infinite cyclic, at every
basepoint. -/
theorem minimalHopfComplement_piOne_mulEquiv_int
    (x : SSet.toTop.obj (orderedSSet minimalHopfComplementPreimageFacets)) :
    Nonempty
      (HomotopyGroup.Pi 1
          (SSet.toTop.obj (orderedSSet minimalHopfComplementPreimageFacets)) x ≃*
        Multiplicative ℤ) := by
  let e := minimalHopfComplementRealizationHomotopyEquivSphereOne
  obtain ⟨changeSpace⟩ := nonempty_mulEquiv_of_homotopyEquiv'
    (N := Fin 1) e x
  obtain ⟨circle⟩ := pi1_sphere_one_mulEquiv_int_at (e x)
  exact ⟨changeSpace.trans circle⟩

/-- Every homotopy group above degree one of the complementary finite Hopf piece vanishes, at
every basepoint. -/
theorem minimalHopfComplement_higher_homotopy_subsingleton
    (k : ℕ)
    (x : SSet.toTop.obj (orderedSSet minimalHopfComplementPreimageFacets)) :
    Subsingleton
      (HomotopyGroup.Pi (k + 2)
        (SSet.toTop.obj (orderedSSet minimalHopfComplementPreimageFacets)) x) := by
  let e := minimalHopfComplementRealizationHomotopyEquivSphereOne
  letI : Subsingleton
      (HomotopyGroup.Pi (k + 2) (SphereSpace 1) (e x)) :=
    sphere_one_higher_homotopy_subsingleton_at k (e x)
  obtain ⟨changeSpace⟩ := nonempty_mulEquiv_of_homotopyEquiv'
    (N := Fin (k + 2)) e x
  exact changeSpace.injective.subsingleton

end Submission.ComplexProjectivePlaneTriangulation
