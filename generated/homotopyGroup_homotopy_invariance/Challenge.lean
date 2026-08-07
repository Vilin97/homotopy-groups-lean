import Mathlib

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

theorem homotopyGroup_homotopy_invariance (n : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (e : X ≃ₕ Y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) X x ≃*
        HomotopyGroup.Pi (n + 1) Y (e x)) := by
  sorry
