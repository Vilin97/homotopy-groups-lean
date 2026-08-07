import Mathlib
import Submission

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

theorem homotopyGroup_loop_shift (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :
    Nonempty
      (HomotopyGroup.Pi (n + 1)
          (GenLoop (Fin 1) X x) GenLoop.const ≃*
        HomotopyGroup.Pi (n + 2) X x) := by
  exact Submission.homotopyGroup_loop_shift n X x
