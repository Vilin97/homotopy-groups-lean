import Mathlib
import Submission

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

theorem homotopyGroup_change_basepoint (n : ℕ) (X : Type u) [TopologicalSpace X]
    (x y : X) (p : Path x y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) X x ≃*
        HomotopyGroup.Pi (n + 1) X y) := by
  exact Submission.homotopyGroup_change_basepoint n X x y p
