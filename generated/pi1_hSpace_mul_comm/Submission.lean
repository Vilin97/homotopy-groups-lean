import Mathlib
import Submission.Helpers

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

namespace Submission

theorem pi1_hSpace_mul_comm (X : Type u) [TopologicalSpace X] [HSpace X]
    (a b : HomotopyGroup.Pi 1 X HSpace.e) :
    a * b = b * a := by
  sorry

end Submission
