import Mathlib

open scoped ContinuousMap Topology Topology.Homotopy

universe u

namespace Submission

/-- Mathlib's one-dimensional cubical homotopy group is multiplicatively
equivalent to the path-based fundamental group. -/
theorem pi1_mulEquiv_fundamentalGroup
    (X : Type u) [TopologicalSpace X] (x : X) :
    Nonempty
      (HomotopyGroup.Pi 1 X x ≃* FundamentalGroup X x) := by
  exact ⟨HomotopyGroup.pi1MulEquivFundamentalGroup⟩

end Submission
