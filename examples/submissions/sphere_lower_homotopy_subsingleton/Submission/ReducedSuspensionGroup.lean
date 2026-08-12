/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Topology.Homotopy.HomotopyGroup
import Submission.Model.ReducedSuspension

/-!
# Reduced suspension on cubical homotopy groups

A generalized `N`-loop in `X` suspends to an `Option N`-loop in the reduced suspension by using
the `none` coordinate as the suspension coordinate.  Collapsing the basepoint meridian is the
key feature: it makes the construction send the constant loop to the constant loop and commute
strictly with concatenation in every old coordinate.

The construction respects homotopies relative to the cubical boundary, so it descends to
homotopy classes and bundles as a monoid homomorphism in positive dimensions.
-/

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

open unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

namespace GenLoop

variable {N : Type*} {x₀ : X}

/-- Forget the new suspension coordinate of an `Option N`-cube. -/
def optionTail (t : I^(Option N)) : I^N :=
  fun i => t (some i)

@[simp]
theorem optionTail_apply (t : I^(Option N)) (i : N) : optionTail t i = t (some i) :=
  rfl

@[fun_prop]
theorem continuous_optionTail : Continuous (fun t : I^(Option N) => optionTail t) := by
  unfold optionTail
  fun_prop

@[simp]
theorem optionTail_update_some [DecidableEq N] (t : I^(Option N)) (i : N) (s : I) :
    optionTail (Function.update t (some i) s) = Function.update (optionTail t) i s := by
  funext j
  simp [optionTail, Function.update]

/-- Add a suspension coordinate to a generalized loop, landing in reduced suspension. -/
def reducedSuspension (p : Ω^ N X x₀) :
    Ω^ (Option N) (ReducedSusp X x₀) (ReducedSusp.base x₀) :=
  ⟨⟨fun t => ReducedSusp.mk x₀ (t none, p (optionTail t)),
      (ReducedSusp.mk x₀).continuous.comp
        ((continuous_apply none).prodMk (p.1.continuous.comp continuous_optionTail))⟩, by
    rintro t ⟨i, hi⟩
    cases i with
    | none =>
        rcases hi with hi | hi
        · exact ReducedSusp.mk_eq_base_of_collapsed x₀ (Or.inl hi)
        · exact ReducedSusp.mk_eq_base_of_collapsed x₀ (Or.inr (Or.inl hi))
    | some i =>
        apply ReducedSusp.mk_eq_base_of_collapsed
        right
        right
        apply p.property
        exact ⟨i, hi⟩⟩

@[simp]
theorem reducedSuspension_apply (p : Ω^ N X x₀) (t : I^(Option N)) :
    reducedSuspension p t = ReducedSusp.mk x₀ (t none, p (optionTail t)) :=
  rfl

@[simp]
theorem reducedSuspension_const :
    reducedSuspension
      (GenLoop.const : Ω^ N X x₀) =
      (GenLoop.const : Ω^ (Option N) (ReducedSusp X x₀) (ReducedSusp.base x₀)) := by
  apply GenLoop.ext
  intro t
  change ReducedSusp.mk x₀ (t none, x₀) = ReducedSusp.base x₀
  exact ReducedSusp.mk_base x₀ (t none)

/-- Reduced suspension preserves cubical homotopies relative to the boundary. -/
theorem reducedSuspension_homotopic {p q : Ω^ N X x₀}
    (H : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (reducedSuspension p) (reducedSuspension q) := by
  obtain ⟨H⟩ := H
  refine ⟨⟨⟨fun st => ReducedSusp.mk x₀
    (st.2 none, H (st.1, optionTail st.2)), ?_⟩, ?_, ?_⟩, ?_⟩
  · exact (ReducedSusp.mk x₀).continuous.comp
      (((continuous_apply none).comp continuous_snd).prodMk
        (H.continuous.comp
          (continuous_fst.prodMk (continuous_optionTail.comp continuous_snd))))
  · intro t
    change ReducedSusp.mk x₀ (t none, H (0, optionTail t)) =
      ReducedSusp.mk x₀ (t none, p (optionTail t))
    exact congrArg (fun z => ReducedSusp.mk x₀ (t none, z)) (H.map_zero_left _)
  · intro t
    change ReducedSusp.mk x₀ (t none, H (1, optionTail t)) =
      ReducedSusp.mk x₀ (t none, q (optionTail t))
    exact congrArg (fun z => ReducedSusp.mk x₀ (t none, z)) (H.map_one_left _)
  · intro s t ht
    calc
      ReducedSusp.mk x₀ (t none, H (s, optionTail t)) =
          ReducedSusp.base x₀ := by
        rcases ht with ⟨i, hi⟩
        cases i with
        | none =>
            rcases hi with hi | hi
            · exact ReducedSusp.mk_eq_base_of_collapsed x₀ (Or.inl hi)
            · exact ReducedSusp.mk_eq_base_of_collapsed x₀ (Or.inr (Or.inl hi))
        | some i =>
            apply ReducedSusp.mk_eq_base_of_collapsed
            right
            right
            calc
              H (s, optionTail t) = p (optionTail t) := H.eq_fst s ⟨i, hi⟩
              _ = x₀ := p.property _ ⟨i, hi⟩
      _ = reducedSuspension p t := ((reducedSuspension p).property t ht).symm

variable [DecidableEq N]

/-- Adding a suspension coordinate commutes strictly with concatenation in an old coordinate. -/
theorem reducedSuspension_transAt (i : N) (p q : Ω^ N X x₀) :
    reducedSuspension (GenLoop.transAt i p q) =
      GenLoop.transAt (some i) (reducedSuspension p) (reducedSuspension q) := by
  apply GenLoop.ext
  intro t
  simp only [reducedSuspension_apply, GenLoop.transAt, GenLoop.coe_copy]
  rw [optionTail_apply]
  split_ifs <;> simp

end GenLoop

namespace HomotopyGroup

variable {N : Type*} {x₀ : X}

/-- Suspension on homotopy classes, with target indexed by the added `Option` coordinate. -/
def reducedSuspension :
    HomotopyGroup N X x₀ →
      HomotopyGroup (Option N) (ReducedSusp X x₀) (ReducedSusp.base x₀) :=
  Quotient.map GenLoop.reducedSuspension fun _ _ H => GenLoop.reducedSuspension_homotopic H

@[simp]
theorem reducedSuspension_mk (p : Ω^ N X x₀) :
    reducedSuspension (⟦p⟧ : HomotopyGroup N X x₀) = ⟦GenLoop.reducedSuspension p⟧ :=
  rfl

/-- Reduced suspension is a monoid homomorphism on positive-dimensional homotopy groups. -/
def reducedSuspensionHom [DecidableEq N] [Nonempty N] :
    HomotopyGroup N X x₀ →*
      HomotopyGroup (Option N) (ReducedSusp X x₀) (ReducedSusp.base x₀) where
  toFun := reducedSuspension
  map_one' := by
    rw [_root_.HomotopyGroup.one_def, reducedSuspension_mk,
      GenLoop.reducedSuspension_const]
    exact _root_.HomotopyGroup.one_def.symm
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    simp only [_root_.HomotopyGroup.mul_spec (i := Classical.arbitrary N),
      reducedSuspension_mk, GenLoop.reducedSuspension_transAt]
    exact (_root_.HomotopyGroup.mul_spec (i := some (Classical.arbitrary N))).symm

@[simp]
theorem reducedSuspensionHom_apply [DecidableEq N] [Nonempty N]
    (a : HomotopyGroup N X x₀) : reducedSuspensionHom a = reducedSuspension a :=
  rfl

end HomotopyGroup

end Submission
