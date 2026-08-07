import Mathlib
import Submission

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

theorem pi1_mulEquiv_fundamentalGroup (X : Type u) [TopologicalSpace X] (x : X) :
    Nonempty
      (HomotopyGroup.Pi 1 X x ≃* FundamentalGroup X x) := by
  exact Submission.pi1_mulEquiv_fundamentalGroup X x
