import Mathlib
import Submission

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

theorem pi1_simplyConnected_subsingleton (X : Type u) [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup.Pi 1 X x) := by
  exact Submission.pi1_simplyConnected_subsingleton X x
