import EvalTools.Markers
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.HSpaces
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Foundational homotopy-group challenges

This module records structural results that should connect mathlib's generalized-loop
definition of `HomotopyGroup` to the standard functorial API.  In the pinned mathlib,
the zeroth- and first-homotopy-group comparison equivalences exist, as do the group
and commutative-group instances.  Higher induced maps, basepoint change, and the
quotient-level product and loop-space equivalences do not yet exist.
-/

open scoped ContinuousMap Topology Topology.Homotopy

namespace HomotopyGroups

universe u v

@[eval_problem]
theorem pi0_equiv_zerothHomotopy
    (X : Type u) [TopologicalSpace X] (x : X) :
    Nonempty (HomotopyGroup.Pi 0 X x ≃ ZerothHomotopy X) := by
  sorry

@[eval_problem]
theorem pi1_mulEquiv_fundamentalGroup
    (X : Type u) [TopologicalSpace X] (x : X) :
    Nonempty
      (HomotopyGroup.Pi 1 X x ≃* FundamentalGroup X x) := by
  sorry

@[eval_problem]
theorem pi0_pathConnected_subsingleton
    (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup.Pi 0 X x) := by
  sorry

@[eval_problem]
theorem pi1_simplyConnected_subsingleton
    (X : Type u) [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup.Pi 1 X x) := by
  sorry

@[eval_problem]
theorem higher_homotopy_mul_comm
    (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X)
    (a b : HomotopyGroup.Pi (n + 2) X x) :
    a * b = b * a := by
  sorry

@[eval_problem]
theorem pi1_hSpace_mul_comm
    (X : Type u) [TopologicalSpace X] [HSpace X]
    (a b : HomotopyGroup.Pi 1 X HSpace.e) :
    a * b = b * a := by
  sorry

@[eval_problem]
theorem homotopyGroup_homotopy_invariance
    (n : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (e : X ≃ₕ Y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) X x ≃*
        HomotopyGroup.Pi (n + 1) Y (e x)) := by
  sorry

@[eval_problem]
theorem homotopyGroup_change_basepoint
    (n : ℕ) (X : Type u) [TopologicalSpace X]
    (x y : X) (p : Path x y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) X x ≃*
        HomotopyGroup.Pi (n + 1) X y) := by
  sorry

@[eval_problem]
theorem homotopyGroup_product
    (n : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (X × Y) (x, y) ≃*
        HomotopyGroup.Pi (n + 1) X x ×
          HomotopyGroup.Pi (n + 1) Y y) := by
  sorry

@[eval_problem]
theorem homotopyGroup_loop_shift
    (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :
    Nonempty
      (HomotopyGroup.Pi (n + 1)
          (GenLoop (Fin 1) X x) GenLoop.const ≃*
        HomotopyGroup.Pi (n + 2) X x) := by
  sorry

end HomotopyGroups
