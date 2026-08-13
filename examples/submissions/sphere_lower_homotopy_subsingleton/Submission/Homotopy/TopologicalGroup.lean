/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ForMathlib.HomotopyGroup.Basic
import Mathlib.GroupTheory.EckmannHilton
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Homotopy groups of topological groups

For a topological group, generalized loops can be multiplied and inverted pointwise.  The
Eckmann--Hilton argument identifies this pointwise multiplication with the usual concatenation
operation on every positive-dimensional homotopy group.  Consequently pointwise inversion
represents the group inverse.
-/

open scoped Topology Topology.Homotopy
open unitInterval

namespace Submission

namespace GenLoop

variable {N G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- Pointwise multiplication of generalized loops in a topological group. -/
def pointwiseMul (p q : Ω^ N G (1 : G)) : Ω^ N G (1 : G) where
  val := ⟨fun t ↦ p.1 t * q.1 t, by fun_prop⟩
  property t ht := by
    change p.1 t * q.1 t = 1
    rw [p.property t ht, q.property t ht, one_mul]

@[simp]
theorem pointwiseMul_apply (p q : Ω^ N G (1 : G)) (t : I^N) :
    pointwiseMul p q t = p t * q t :=
  rfl

/-- Pointwise inversion of a generalized loop in a topological group. -/
def pointwiseInv (p : Ω^ N G (1 : G)) : Ω^ N G (1 : G) where
  val := ⟨fun t ↦ (p.1 t)⁻¹, by fun_prop⟩
  property t ht := by
    change (p.1 t)⁻¹ = 1
    rw [p.property t ht, inv_one]

@[simp]
theorem pointwiseInv_apply (p : Ω^ N G (1 : G)) (t : I^N) :
    pointwiseInv p t = (p t)⁻¹ :=
  rfl

/-- Pointwise multiplication preserves homotopies relative to the cube boundary. -/
theorem Homotopic.pointwiseMul {p p' q q' : Ω^ N G (1 : G)}
    (hp : _root_.GenLoop.Homotopic p p') (hq : _root_.GenLoop.Homotopic q q') :
    _root_.GenLoop.Homotopic (pointwiseMul p q) (pointwiseMul p' q') := by
  obtain ⟨Hp⟩ := hp
  obtain ⟨Hq⟩ := hq
  exact ⟨
    { toFun := fun st ↦ Hp st * Hq st
      continuous_toFun := by fun_prop
      map_zero_left := fun t ↦ by
        change Hp (0, t) * Hq (0, t) = p.1 t * q.1 t
        rw [Hp.apply_zero, Hq.apply_zero]
      map_one_left := fun t ↦ by
        change Hp (1, t) * Hq (1, t) = p'.1 t * q'.1 t
        rw [Hp.apply_one, Hq.apply_one]
      prop' := fun s t ht ↦ by
        change Hp (s, t) * Hq (s, t) = p.1 t * q.1 t
        rw [Hp.eq_fst s ht, Hq.eq_fst s ht] }⟩

/-- Pointwise inversion preserves homotopies relative to the cube boundary. -/
theorem Homotopic.pointwiseInv {p q : Ω^ N G (1 : G)}
    (h : _root_.GenLoop.Homotopic p q) :
    _root_.GenLoop.Homotopic (pointwiseInv p) (pointwiseInv q) := by
  obtain ⟨H⟩ := h
  exact ⟨
    { toFun := fun st ↦ (H st)⁻¹
      continuous_toFun := by fun_prop
      map_zero_left := fun t ↦ by
        change (H (0, t))⁻¹ = (p.1 t)⁻¹
        rw [H.apply_zero]
      map_one_left := fun t ↦ by
        change (H (1, t))⁻¹ = (q.1 t)⁻¹
        rw [H.apply_one]
      prop' := fun s t ht ↦ by
        change (H (s, t))⁻¹ = (p.1 t)⁻¹
        rw [H.eq_fst s ht] }⟩

/-- Pointwise multiplication distributes strictly over cubical concatenation. -/
theorem pointwiseMul_transAt [DecidableEq N] (i : N)
    (a b c d : Ω^ N G (1 : G)) :
    pointwiseMul (_root_.GenLoop.transAt i a b) (_root_.GenLoop.transAt i c d) =
      _root_.GenLoop.transAt i (pointwiseMul a c) (pointwiseMul b d) := by
  ext t
  change (_root_.GenLoop.transAt i a b t) * (_root_.GenLoop.transAt i c d t) =
    _root_.GenLoop.transAt i (pointwiseMul a c) (pointwiseMul b d) t
  simp only [_root_.GenLoop.transAt, _root_.GenLoop.coe_copy]
  split_ifs <;> rfl

end GenLoop

namespace HomotopyGroup

variable {N G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- Pointwise multiplication descended to homotopy classes. -/
def pointwiseMulClass
    (a b : HomotopyGroup N G (1 : G)) : HomotopyGroup N G (1 : G) :=
  Quotient.liftOn₂ a b
    (fun p q ↦ ⟦GenLoop.pointwiseMul p q⟧)
    (fun _ _ _ _ hp hq ↦
      Quotient.sound (Submission.GenLoop.Homotopic.pointwiseMul hp hq))

@[simp]
theorem pointwiseMulClass_mk (p q : Ω^ N G (1 : G)) :
    pointwiseMulClass (⟦p⟧ : HomotopyGroup N G (1 : G)) ⟦q⟧ =
      ⟦GenLoop.pointwiseMul p q⟧ :=
  rfl

/-- Pointwise multiplication has the constant class as a strict two-sided unit. -/
theorem pointwiseMulClass_isUnital :
    EckmannHilton.IsUnital pointwiseMulClass
      (⟦_root_.GenLoop.const⟧ : HomotopyGroup N G (1 : G)) where
  left_id := by
    rintro ⟨p⟩
    change ⟦GenLoop.pointwiseMul _root_.GenLoop.const p⟧ = ⟦p⟧
    apply congrArg Quotient.mk'
    ext t
    simp
  right_id := by
    rintro ⟨p⟩
    change ⟦GenLoop.pointwiseMul p _root_.GenLoop.const⟧ = ⟦p⟧
    apply congrArg Quotient.mk'
    ext t
    simp

/-- Pointwise multiplication satisfies the interchange law with cubical concatenation. -/
theorem pointwiseMulClass_interchange [DecidableEq N] [Nonempty N]
    (a b c d : HomotopyGroup N G (1 : G)) :
    pointwiseMulClass (a * b) (c * d) =
      pointwiseMulClass a c * pointwiseMulClass b d := by
  refine Quotient.inductionOn a fun p ↦ ?_
  refine Quotient.inductionOn b fun q ↦ ?_
  refine Quotient.inductionOn c fun r ↦ ?_
  refine Quotient.inductionOn d fun s ↦ ?_
  simp only [_root_.HomotopyGroup.mul_spec (i := Classical.arbitrary N),
    pointwiseMulClass_mk]
  apply congrArg Quotient.mk'
  exact GenLoop.pointwiseMul_transAt (Classical.arbitrary N) q p s r

/-- On every positive-dimensional homotopy group of a topological group, pointwise
multiplication is the ordinary homotopy-group multiplication. -/
theorem pointwiseMulClass_eq_mul [DecidableEq N] [Nonempty N] :
    pointwiseMulClass =
      ((· * ·) : HomotopyGroup N G (1 : G) → HomotopyGroup N G (1 : G) →
        HomotopyGroup N G (1 : G)) :=
  EckmannHilton.mul pointwiseMulClass_isUnital
    EckmannHilton.MulOneClass.isUnital pointwiseMulClass_interchange

/-- Pointwise inversion of a representative pointwise-multiplied by that representative is the
constant homotopy class. -/
theorem pointwiseMulClass_pointwiseInv (p : Ω^ N G (1 : G)) :
    pointwiseMulClass
        (⟦GenLoop.pointwiseInv p⟧ : HomotopyGroup N G (1 : G))
        (⟦p⟧ : HomotopyGroup N G (1 : G)) =
      (⟦_root_.GenLoop.const⟧ : HomotopyGroup N G (1 : G)) := by
  change (⟦GenLoop.pointwiseMul (GenLoop.pointwiseInv p) p⟧ :
      HomotopyGroup N G (1 : G)) = ⟦_root_.GenLoop.const⟧
  apply congrArg Quotient.mk'
  ext t
  simp

end HomotopyGroup

end Submission
