import Mathlib
import Submission.Helpers

open scoped ContinuousMap Topology Topology.Homotopy

universe u

namespace Submission

/-- Transport the native fundamental-group subsingleton structure across the
multiplicative equivalence `π₁(X,x) ≃* FundamentalGroup X x`. -/
theorem pi1_simplyConnected_subsingleton
    (X : Type u) [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup.Pi 1 X x) := by
  exact HomotopyGroup.pi1MulEquivFundamentalGroup.injective.subsingleton

end Submission
