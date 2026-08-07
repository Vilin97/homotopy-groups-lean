import Mathlib
import Submission

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

theorem higher_homotopy_mul_comm (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X)
    (a b : HomotopyGroup.Pi (n + 2) X x) :
    a * b = b * a := by
  exact Submission.higher_homotopy_mul_comm n X x a b
