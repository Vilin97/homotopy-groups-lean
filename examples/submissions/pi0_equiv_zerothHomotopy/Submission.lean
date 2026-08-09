import Mathlib

open scoped ContinuousMap Topology Topology.Homotopy

universe u

namespace Submission

/-- Mathlib's cubical zeroth homotopy group is equivalent to the type of path
components. -/
theorem pi0_equiv_zerothHomotopy
    (X : Type u) [TopologicalSpace X] (x : X) :
    Nonempty (HomotopyGroup.Pi 0 X x ≃ ZerothHomotopy X) := by
  exact ⟨HomotopyGroup.pi0EquivZerothHomotopy⟩

end Submission
