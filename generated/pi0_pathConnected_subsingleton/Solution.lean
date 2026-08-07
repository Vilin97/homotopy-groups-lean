import Mathlib
import Submission

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

theorem pi0_pathConnected_subsingleton (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup.Pi 0 X x) := by
  exact Submission.pi0_pathConnected_subsingleton X x
