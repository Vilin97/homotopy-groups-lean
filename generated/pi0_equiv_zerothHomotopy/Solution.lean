import Mathlib
import Submission

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

theorem pi0_equiv_zerothHomotopy (X : Type u) [TopologicalSpace X] (x : X) :
    Nonempty (HomotopyGroup.Pi 0 X x ≃ ZerothHomotopy X) := by
  exact Submission.pi0_equiv_zerothHomotopy X x
