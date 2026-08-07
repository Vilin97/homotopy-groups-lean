import Mathlib
import Submission.Helpers

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

namespace Submission

theorem homotopyGroup_product (n : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (X × Y) (x, y) ≃*
        HomotopyGroup.Pi (n + 1) X x ×
          HomotopyGroup.Pi (n + 1) Y y) := by
  sorry

end Submission
