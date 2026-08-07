import Mathlib
import Submission.Helpers

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

namespace Submission

theorem homotopyGroup_change_basepoint (n : ℕ) (X : Type u) [TopologicalSpace X]
    (x y : X) (p : Path x y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) X x ≃*
        HomotopyGroup.Pi (n + 1) X y) := by
  sorry

end Submission
