import Mathlib
import Submission.Helpers

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

namespace Submission

theorem pi1_simplyConnected_subsingleton (X : Type u) [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup.Pi 1 X x) := by
  sorry

end Submission
