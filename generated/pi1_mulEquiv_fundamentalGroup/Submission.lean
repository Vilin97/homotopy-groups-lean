import Mathlib
import Submission.Helpers

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

namespace Submission

theorem pi1_mulEquiv_fundamentalGroup (X : Type u) [TopologicalSpace X] (x : X) :
    Nonempty
      (HomotopyGroup.Pi 1 X x ≃* FundamentalGroup X x) := by
  sorry

end Submission
