import Mathlib
import Submission.Helpers

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

namespace Submission

theorem pi0_equiv_zerothHomotopy (X : Type u) [TopologicalSpace X] (x : X) :
    Nonempty (HomotopyGroup.Pi 0 X x ≃ ZerothHomotopy X) := by
  sorry

end Submission
