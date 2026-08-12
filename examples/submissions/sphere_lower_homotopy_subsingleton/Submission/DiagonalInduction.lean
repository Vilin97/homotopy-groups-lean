/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.MetricSpherePiOne
import Submission.Pi2SphereTwo

/-!
# The exact algebraic induction needed for the sphere diagonal

The geometric obstruction to extending the displayed diagonal is now isolated in one place.
Once successive suspension maps are proved to be multiplicative equivalences, the first exact
metric-circle calculation propagates uniformly to every diagonal group.

This file does not assume that the missing suspension equivalences already exist.  It proves the
honest implication consumed by that future geometric theorem, and separately records the first
available transition `π₁(S¹) ≃ π₂(S²)` from the two computations already checked in this project.
-/

open HomotopyGroups

noncomputable section

namespace Submission

/-- The two currently computed diagonal groups give an exact equivalence
`π₁(S¹) ≃ π₂(S²)` in the benchmark's metric-sphere model. -/
theorem sphere_diagonal_one_two_mulEquiv :
    Nonempty
      (HomotopyGroup.Pi 1 (SphereSpace 1) (sphereBasepoint 1) ≃*
        HomotopyGroup.Pi 2 (SphereSpace 2) (sphereBasepoint 2)) := by
  obtain ⟨circle⟩ := pi1_sphere_one_mulEquiv_int
  obtain ⟨sphereTwo⟩ := pi2_sphere_two_mulEquiv_int
  exact ⟨circle.trans sphereTwo.symm⟩

/-- A uniform family of successive diagonal equivalences propagates the exact circle result to
every metric-sphere diagonal group.  This isolates the remaining geometric task: construct the
successive equivalences, for example from a formal Freudenthal suspension theorem. -/
theorem sphere_diagonal_mulEquiv_int_of_suspension_steps
    (step : ∀ n : ℕ, Nonempty
      (HomotopyGroup.Pi (n + 1) (SphereSpace (n + 1)) (sphereBasepoint (n + 1)) ≃*
        HomotopyGroup.Pi (n + 2) (SphereSpace (n + 2)) (sphereBasepoint (n + 2))))
    (n : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (SphereSpace (n + 1)) (sphereBasepoint (n + 1)) ≃*
        Multiplicative ℤ) := by
  induction n with
  | zero => simpa using pi1_sphere_one_mulEquiv_int
  | succ n ih =>
      obtain ⟨suspension⟩ := step n
      obtain ⟨previous⟩ := ih
      exact ⟨suspension.symm.trans previous⟩

end Submission
