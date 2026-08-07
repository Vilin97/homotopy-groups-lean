import Mathlib

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

theorem homotopyGroup_change_basepoint (n : ℕ) (X : Type u) [TopologicalSpace X]
    (x y : X) (p : Path x y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) X x ≃*
        HomotopyGroup.Pi (n + 1) X y) := by
  sorry
