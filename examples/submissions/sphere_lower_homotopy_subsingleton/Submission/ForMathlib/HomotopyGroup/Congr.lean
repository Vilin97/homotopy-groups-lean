/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Reindexing cubical homotopy groups

Mathlib provides the homeomorphism `GenLoop.congr` between generalized loop spaces indexed by
equivalent types.  This file proves that it preserves boundary-relative homotopy and corresponding
coordinate concatenation.  It therefore descends to a multiplicative equivalence of homotopy
groups in positive dimensions.
-/

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

namespace GenLoop

variable {M N X : Type*} [TopologicalSpace X] {x : X}

@[simp]
theorem congr_apply (e : M ≃ N) (p : Ω^ M X x) (t : I^N) :
    GenLoop.congr x e p t = p (fun m => t (e m)) :=
  rfl

/-- Reindexing a cube preserves homotopies relative to its boundary. -/
theorem congr_homotopic (e : M ≃ N) {p q : Ω^ M X x}
    (H : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (GenLoop.congr x e p) (GenLoop.congr x e q) := by
  obtain ⟨H⟩ := H
  refine ⟨⟨⟨fun st => H (st.1, fun m => st.2 (e m)), ?_⟩, ?_, ?_⟩, ?_⟩
  · fun_prop
  · intro t
    exact H.map_zero_left _
  · intro t
    exact H.map_one_left _
  · rintro s t ⟨i, hi⟩
    exact H.eq_fst s ⟨e.symm i, by simpa using hi⟩

variable [DecidableEq M] [DecidableEq N]

/-- Reindexing commutes strictly with concatenation in the corresponding coordinate. -/
theorem congr_transAt (e : M ≃ N) (i : M) (p q : Ω^ M X x) :
    GenLoop.congr x e (GenLoop.transAt i p q) =
      GenLoop.transAt (e i) (GenLoop.congr x e p) (GenLoop.congr x e q) := by
  apply GenLoop.ext
  intro t
  have hupdate (s : I) :
      (fun m => Function.update t (e i) s (e m)) =
        Function.update (fun m => t (e m)) i s := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · have heji : e j ≠ e i := fun h => hji (e.injective h)
      simp [Function.update, hji, heji]
  simp only [GenLoop.congr_apply, GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rw [hupdate]

end GenLoop

namespace HomotopyGroup

variable {M N X : Type*} [TopologicalSpace X] {x : X}

/-- Reindex a cubical homotopy class along an equivalence of coordinate types. -/
def congr (e : M ≃ N) : HomotopyGroup M X x → HomotopyGroup N X x :=
  Quotient.map (GenLoop.congr x e) fun _ _ H => GenLoop.congr_homotopic e H

@[simp]
theorem congr_mk (e : M ≃ N) (p : Ω^ M X x) :
    congr e (⟦p⟧ : HomotopyGroup M X x) = ⟦GenLoop.congr x e p⟧ :=
  rfl

@[simp]
theorem congr_symm_apply (e : M ≃ N) (a : HomotopyGroup M X x) :
    congr e.symm (congr e a) = a := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [congr_mk, congr_mk]
  apply congrArg Quotient.mk'
  apply GenLoop.ext
  intro t
  simp [GenLoop.congr]

@[simp]
theorem congr_apply_symm (e : M ≃ N) (a : HomotopyGroup N X x) :
    congr e (congr e.symm a) = a := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [congr_mk, congr_mk]
  apply congrArg Quotient.mk'
  apply GenLoop.ext
  intro t
  simp [GenLoop.congr]

/-- Reindexing is a monoid homomorphism in positive dimensions. -/
def congrHom [DecidableEq M] [DecidableEq N] [Nonempty M] [Nonempty N] (e : M ≃ N) :
    HomotopyGroup M X x →* HomotopyGroup N X x where
  toFun := congr e
  map_one' := by
    rw [_root_.HomotopyGroup.one_def, congr_mk]
    have h : GenLoop.congr x e
        (GenLoop.const : Ω^ M X x) = (GenLoop.const : Ω^ N X x) := by
      apply GenLoop.ext
      intro t
      rfl
    rw [h]
    exact _root_.HomotopyGroup.one_def.symm
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    simp only [_root_.HomotopyGroup.mul_spec (i := Classical.arbitrary M), congr_mk,
      GenLoop.congr_transAt]
    exact (_root_.HomotopyGroup.mul_spec (i := e (Classical.arbitrary M))).symm

/-- Cubical homotopy groups are multiplicatively equivalent after reindexing coordinates. -/
def congrMulEquiv [DecidableEq M] [DecidableEq N] [Nonempty M] [Nonempty N] (e : M ≃ N) :
    HomotopyGroup M X x ≃* HomotopyGroup N X x :=
  MulEquiv.ofBijective (congrHom e)
    ⟨fun _ _ h => by
        change congr e _ = congr e _ at h
        have h' := congrArg (congr e.symm) h
        rw [congr_symm_apply, congr_symm_apply] at h'
        exact h',
      fun b => ⟨congr e.symm b, congr_apply_symm e b⟩⟩

end HomotopyGroup

end Submission
