import Mathlib
import Submission.Helpers

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

namespace Submission

theorem pi0_pathConnected_subsingleton (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup.Pi 0 X x) := by
  sorry

end Submission
