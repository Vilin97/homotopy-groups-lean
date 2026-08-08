import Mathlib
import Submission.Helpers

open scoped ContinuousMap Topology Topology.Homotopy

universe u

namespace Submission

/-- Transport the native path-component subsingleton structure across the
equivalence between `π₀` and `ZerothHomotopy`. -/
theorem pi0_pathConnected_subsingleton
    (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup.Pi 0 X x) := by
  exact HomotopyGroup.pi0EquivZerothHomotopy.injective.subsingleton

end Submission
