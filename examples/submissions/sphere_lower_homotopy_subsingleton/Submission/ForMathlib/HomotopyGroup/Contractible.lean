/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ForMathlib.HomotopyGroup.Basic
import Mathlib.Topology.Homotopy.Contractible

/-!
# Homotopy groups of a contractible space

All higher homotopy groups of a contractible space are trivial. This is an immediate consequence
of homotopy invariance (`Submission.nonempty_mulEquiv_of_homotopyEquiv'`) together with the fact
that a subsingleton space has trivial homotopy groups.
-/

open scoped Topology.Homotopy

namespace Submission

variable {N : Type*} [DecidableEq N] [Nonempty N]

omit [DecidableEq N] [Nonempty N] in
/-- Every generalized loop in a subsingleton space is the constant one. -/
theorem subsingleton_homotopyGroup_of_subsingleton {X : Type*} [TopologicalSpace X]
    [Subsingleton X] (x : X) : Subsingleton (HomotopyGroup N X x) := by
  refine ⟨fun a b => ?_⟩
  refine Quotient.inductionOn₂ a b fun p q => ?_
  refine Quotient.sound ⟨⟨⟨⟨fun st => p st.2, by fun_prop⟩, fun _ => rfl, fun t => ?_⟩,
    fun s t _ => rfl⟩⟩
  exact Subsingleton.elim _ _

/-- All higher homotopy groups of a contractible space are trivial. -/
theorem subsingleton_homotopyGroup_of_contractible {X : Type*} [TopologicalSpace X]
    [ContractibleSpace X] (x : X) : Subsingleton (HomotopyGroup N X x) := by
  obtain ⟨e⟩ := (inferInstance : ContractibleSpace X).hequiv_unit
  obtain ⟨φ⟩ := nonempty_mulEquiv_of_homotopyEquiv' (N := N) e x
  have : Subsingleton (HomotopyGroup N Unit (e x)) :=
    subsingleton_homotopyGroup_of_subsingleton _
  exact φ.toEquiv.subsingleton

end Submission
