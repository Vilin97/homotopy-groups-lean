/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Maps.Basic

/-!
# Reduced suspension of a pointed space

This file defines the reduced suspension of a pointed topological space as the quotient of
`I × X` which identifies both ends of the interval and the meridian through the basepoint.
The quotient map and its basic universal properties are exposed for later constructions on
homotopy groups.
-/

open scoped Topology unitInterval

noncomputable section

namespace Submission

open unitInterval

universe u

variable {X : Type u}

/-- The subset of the cylinder collapsed in the reduced suspension. -/
def ReducedSuspCollapsed (x₀ : X) (p : I × X) : Prop :=
  p.1 = 0 ∨ p.1 = 1 ∨ p.2 = x₀

/-- The equivalence relation underlying reduced suspension. -/
def ReducedSuspRel (x₀ : X) (a b : I × X) : Prop :=
  a = b ∨ ReducedSuspCollapsed x₀ a ∧ ReducedSuspCollapsed x₀ b

theorem reducedSuspRel_equivalence (x₀ : X) : Equivalence (ReducedSuspRel x₀) where
  refl _ := Or.inl rfl
  symm := by
    intro a b h
    rcases h with rfl | ⟨ha, hb⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hb, ha⟩
  trans := by
    intro a b c hab hbc
    rcases hab with rfl | ⟨ha, hb⟩
    · exact hbc
    · rcases hbc with rfl | ⟨_, hc⟩
      · exact Or.inr ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hc⟩

/-- The setoid on the cylinder whose quotient is reduced suspension. -/
def reducedSuspSetoid (x₀ : X) : Setoid (I × X) :=
  ⟨ReducedSuspRel x₀, reducedSuspRel_equivalence x₀⟩

/-- The reduced suspension of the pointed space `(X, x₀)`. -/
def ReducedSusp (X : Type u) [TopologicalSpace X] (x₀ : X) : Type u :=
  Quotient (reducedSuspSetoid x₀)

variable [TopologicalSpace X]

instance instTopologicalSpaceReducedSusp (x₀ : X) : TopologicalSpace (ReducedSusp X x₀) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

namespace ReducedSusp

/-- The quotient map from the cylinder to reduced suspension. -/
def mk (x₀ : X) : C(I × X, ReducedSusp X x₀) :=
  ⟨fun p => Quotient.mk (reducedSuspSetoid x₀) p, continuous_quot_mk⟩

/-- The distinguished point of reduced suspension. -/
def base (x₀ : X) : ReducedSusp X x₀ :=
  mk x₀ (0, x₀)

theorem mk_eq_base_of_collapsed (x₀ : X) {p : I × X}
    (hp : ReducedSuspCollapsed x₀ p) : mk x₀ p = base x₀ := by
  apply Quotient.sound
  exact Or.inr ⟨hp, Or.inl rfl⟩

@[simp]
theorem mk_zero (x₀ x : X) : mk x₀ (0, x) = base x₀ :=
  mk_eq_base_of_collapsed x₀ (Or.inl rfl)

@[simp]
theorem mk_one (x₀ x : X) : mk x₀ (1, x) = base x₀ :=
  mk_eq_base_of_collapsed x₀ (Or.inr (Or.inl rfl))

@[simp]
theorem mk_base (x₀ : X) (t : I) : mk x₀ (t, x₀) = base x₀ :=
  mk_eq_base_of_collapsed x₀ (Or.inr (Or.inr rfl))

theorem mk_surjective (x₀ : X) : Function.Surjective (mk x₀ : I × X → ReducedSusp X x₀) :=
  Quotient.mk_surjective

theorem isQuotientMap_mk (x₀ : X) :
    Topology.IsQuotientMap (mk x₀ : I × X → ReducedSusp X x₀) :=
  isQuotientMap_quot_mk

end ReducedSusp

end Submission
