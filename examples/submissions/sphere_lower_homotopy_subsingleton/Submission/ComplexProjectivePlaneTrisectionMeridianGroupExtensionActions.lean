/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionMeridianGroupExtensionEquivalences

/-!
# Trivial conjugation actions in the trisection group extensions

The central-interface fundamental group is commutative at every basepoint because it is
multiplicatively equivalent to `Z x Z`.  It follows directly that the conjugation action attached
to each explicit splitting is trivial.

Thus the standard semidirect-product decomposition produced by `GroupExtension.Splitting` is an
ordinary direct product for all three trisection sequences.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped Topology Topology.Homotopy

namespace Submission

/-- A group multiplicatively equivalent to a commutative group has commuting elements. -/
theorem mul_comm_of_mulEquiv_commGroup
    {G A : Type*} [Group G] [CommGroup A]
    (e : G ≃* A) (x y : G) :
    x * y = y * x := by
  apply e.injective
  simp only [map_mul]
  exact mul_comm (e x) (e y)

/-- A splitting through a commutative middle group has trivial conjugation action. -/
theorem groupExtensionSplitting_conjAct_eq_one_of_mul_comm
    {N E G : Type*} [Group N] [Group E] [Group G]
    (S : GroupExtension N E G) (s : S.Splitting)
    (hcomm : ∀ x y : E, x * y = y * x) :
    s.conjAct = 1 := by
  apply MonoidHom.ext
  intro g
  apply MulEquiv.ext
  intro n
  apply S.inl_injective
  change S.inl (S.conjAct (s g) n) = S.inl n
  rw [GroupExtension.inl_conjAct_comm]
  rw [hcomm (s g) (S.inl n), mul_inv_cancel_right]

end Submission

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- Multiplication in the central-interface fundamental group is commutative at every
basepoint. -/
theorem centralInterface_piOne_mul_comm
    (base : SSet.toTop.obj (orderedSSet centralInterfaceFacets))
    (x y : HomotopyGroup.Pi 1
      (SSet.toTop.obj (orderedSSet centralInterfaceFacets)) base) :
    x * y = y * x := by
  obtain ⟨e⟩ := centralInterface_piOne_mulEquiv_int_prod_int base
  exact mul_comm_of_mulEquiv_commGroup e x y

/-- The conjugation action induced by the zero-five splitting is trivial. -/
theorem zeroFiveCentralInterfacePiOneGroupExtensionSplitting_conjAct_eq_one :
    zeroFiveCentralInterfacePiOneGroupExtensionSplitting.conjAct = 1 :=
  groupExtensionSplitting_conjAct_eq_one_of_mul_comm
    zeroFiveCentralInterfacePiOneGroupExtension
    zeroFiveCentralInterfacePiOneGroupExtensionSplitting
    (centralInterface_piOne_mul_comm zeroFiveCentralRealizationBase)

/-- The conjugation action induced by the five-four splitting is trivial. -/
theorem fiveFourCentralInterfacePiOneGroupExtensionSplitting_conjAct_eq_one :
    fiveFourCentralInterfacePiOneGroupExtensionSplitting.conjAct = 1 :=
  groupExtensionSplitting_conjAct_eq_one_of_mul_comm
    fiveFourCentralInterfacePiOneGroupExtension
    fiveFourCentralInterfacePiOneGroupExtensionSplitting
    (centralInterface_piOne_mul_comm fiveFourCentralRealizationBase)

/-- The conjugation action induced by the four-zero splitting is trivial. -/
theorem fourZeroCentralInterfacePiOneGroupExtensionSplitting_conjAct_eq_one :
    fourZeroCentralInterfacePiOneGroupExtensionSplitting.conjAct = 1 :=
  groupExtensionSplitting_conjAct_eq_one_of_mul_comm
    fourZeroCentralInterfacePiOneGroupExtension
    fourZeroCentralInterfacePiOneGroupExtensionSplitting
    (centralInterface_piOne_mul_comm fourZeroCentralRealizationBase)

end Submission.ComplexProjectivePlaneTriangulation
