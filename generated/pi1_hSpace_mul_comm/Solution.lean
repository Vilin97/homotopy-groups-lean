import Mathlib
import Submission

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

theorem pi1_hSpace_mul_comm (X : Type u) [TopologicalSpace X] [HSpace X]
    (a b : HomotopyGroup.Pi 1 X HSpace.e) :
    a * b = b * a := by
  exact Submission.pi1_hSpace_mul_comm X a b
