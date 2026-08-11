/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from the Tau Ceti project (https://github.com/TauCetiProject/TauCeti), Apache 2.0.
-/
import Mathlib.Topology.Homotopy.Product
import Submission.ForMathlib.HomotopyGroup.Map

/-!
# Homotopy groups of products

Generalized loops and homotopies relative to the cube boundary are computed coordinatewise.
This file descends those constructions to binary and indexed products of homotopy groups.
-/

namespace Submission

open scoped unitInterval Topology Topology.Homotopy

namespace GenLoop

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- The coordinatewise product of two generalized loops. -/
def prod (p : Ω^ N X x) (q : Ω^ N Y y) : Ω^ N (X × Y) (x, y) :=
  ⟨ContinuousMap.prodMk p.1 q.1, fun t ht =>
    Prod.ext (_root_.GenLoop.boundary p t ht) (_root_.GenLoop.boundary q t ht)⟩

@[simp]
theorem prod_apply (p : Ω^ N X x) (q : Ω^ N Y y) (t : I^N) :
    prod p q t = (p t, q t) :=
  rfl

@[simp]
theorem map_fst_prod (p : Ω^ N X x) (q : Ω^ N Y y) :
    map (ContinuousMap.fst : C(X × Y, X)) rfl (prod p q) = p := by
  apply _root_.GenLoop.ext
  intro t
  rfl

@[simp]
theorem map_snd_prod (p : Ω^ N X x) (q : Ω^ N Y y) :
    map (ContinuousMap.snd : C(X × Y, Y)) rfl (prod p q) = q := by
  apply _root_.GenLoop.ext
  intro t
  rfl

@[simp]
theorem prod_map_fst_map_snd (p : Ω^ N (X × Y) (x, y)) :
    prod (map (ContinuousMap.fst : C(X × Y, X)) rfl p)
      (map (ContinuousMap.snd : C(X × Y, Y)) rfl p) = p := by
  apply _root_.GenLoop.ext
  intro t
  exact Prod.ext rfl rfl

theorem prod_homotopic {p p' : Ω^ N X x} {q q' : Ω^ N Y y}
    (hp : _root_.GenLoop.Homotopic p p') (hq : _root_.GenLoop.Homotopic q q') :
    _root_.GenLoop.Homotopic (prod p q) (prod p' q') := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨ContinuousMap.HomotopyRel.prod hp hq⟩

variable {J : Type*} {Z : J → Type*} [∀ j, TopologicalSpace (Z j)] {z : ∀ j, Z j}

/-- The coordinatewise indexed product of generalized loops. -/
def pi (p : ∀ j, Ω^ N (Z j) (z j)) : Ω^ N (∀ j, Z j) z :=
  ⟨ContinuousMap.pi fun j => (p j).1, fun t ht =>
    funext fun j => _root_.GenLoop.boundary (p j) t ht⟩

@[simp]
theorem pi_apply (p : ∀ j, Ω^ N (Z j) (z j)) (t : I^N) (j : J) :
    pi p t j = p j t :=
  rfl

@[simp]
theorem map_eval_pi (p : ∀ j, Ω^ N (Z j) (z j)) (j : J) :
    map (ContinuousMap.eval j) rfl (pi p) = p j := by
  apply _root_.GenLoop.ext
  intro t
  rfl

@[simp]
theorem pi_map_eval (p : Ω^ N (∀ j, Z j) z) :
    pi (fun j => map (ContinuousMap.eval j) rfl p) = p := by
  apply _root_.GenLoop.ext
  intro t
  rfl

theorem pi_homotopic {p q : ∀ j, Ω^ N (Z j) (z j)}
    (h : ∀ j, _root_.GenLoop.Homotopic (p j) (q j)) :
    _root_.GenLoop.Homotopic (pi p) (pi q) :=
  ⟨ContinuousMap.HomotopyRel.pi fun j => Classical.choice (h j)⟩

end GenLoop

namespace HomotopyGroup

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- The product of two homotopy classes. -/
def prod (a : HomotopyGroup N X x) (b : HomotopyGroup N Y y) :
    HomotopyGroup N (X × Y) (x, y) :=
  Quotient.map₂ GenLoop.prod
    (fun {p p'} hp {q q'} hq => GenLoop.prod_homotopic (p := p) (p' := p')
      (q := q) (q' := q') hp hq) a b

@[simp]
theorem prod_mk (p : Ω^ N X x) (q : Ω^ N Y y) :
    prod (⟦p⟧ : HomotopyGroup N X x) (⟦q⟧ : HomotopyGroup N Y y) =
      (⟦GenLoop.prod p q⟧ : HomotopyGroup N (X × Y) (x, y)) :=
  rfl

@[simp]
theorem map_fst_prod (a : HomotopyGroup N X x) (b : HomotopyGroup N Y y) :
    map (ContinuousMap.fst : C(X × Y, X)) rfl (prod a b) = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  rw [prod_mk, map_mk, GenLoop.map_fst_prod]
  rfl

@[simp]
theorem map_snd_prod (a : HomotopyGroup N X x) (b : HomotopyGroup N Y y) :
    map (ContinuousMap.snd : C(X × Y, Y)) rfl (prod a b) = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  rw [prod_mk, map_mk, GenLoop.map_snd_prod]
  rfl

@[simp]
theorem prod_map_fst_map_snd (a : HomotopyGroup N (X × Y) (x, y)) :
    prod (map (ContinuousMap.fst : C(X × Y, X)) rfl a)
      (map (ContinuousMap.snd : C(X × Y, Y)) rfl a) = a := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [map_mk, map_mk, prod_mk, GenLoop.prod_map_fst_map_snd]
  rfl

/-- The homotopy group of a binary product is the product of the homotopy groups. -/
def prodEquiv (x : X) (y : Y) :
    HomotopyGroup N (X × Y) (x, y) ≃
      HomotopyGroup N X x × HomotopyGroup N Y y where
  toFun a :=
    (map (ContinuousMap.fst : C(X × Y, X)) rfl a,
      map (ContinuousMap.snd : C(X × Y, Y)) rfl a)
  invFun a := prod a.1 a.2
  left_inv := prod_map_fst_map_snd
  right_inv a := Prod.ext (map_fst_prod a.1 a.2) (map_snd_prod a.1 a.2)

/-- The positive-dimensional multiplicative product equivalence. -/
def prodMulEquiv [DecidableEq N] [Nonempty N] (x : X) (y : Y) :
    HomotopyGroup N (X × Y) (x, y) ≃*
      HomotopyGroup N X x × HomotopyGroup N Y y :=
  { prodEquiv x y with
    map_mul' := fun a b => Prod.ext
      (map_mul (ContinuousMap.fst : C(X × Y, X)) rfl a b)
      (map_mul (ContinuousMap.snd : C(X × Y, Y)) rfl a b) }

variable {J : Type*} {Z : J → Type*} [∀ j, TopologicalSpace (Z j)] {z : ∀ j, Z j}

/-- The indexed product of homotopy classes. -/
noncomputable def pi (a : ∀ j, HomotopyGroup N (Z j) (z j)) :
    HomotopyGroup N (∀ j, Z j) z :=
  (Quotient.map GenLoop.pi fun {p q} h =>
    GenLoop.pi_homotopic (p := p) (q := q) h) (Quotient.choice a)

@[simp]
theorem pi_mk (p : ∀ j, Ω^ N (Z j) (z j)) :
    pi (fun j => (⟦p j⟧ : HomotopyGroup N (Z j) (z j))) =
      (⟦GenLoop.pi p⟧ : HomotopyGroup N (∀ j, Z j) z) := by
  unfold pi
  rw [Quotient.choice_eq, Quotient.map_mk]

@[simp]
theorem map_eval_pi (a : ∀ j, HomotopyGroup N (Z j) (z j)) (j : J) :
    map (ContinuousMap.eval j) rfl (pi a) = a j := by
  induction a using Quotient.induction_on_pi
  simp only [pi_mk, map_mk, GenLoop.map_eval_pi]
  rfl

@[simp]
theorem pi_map_eval (a : HomotopyGroup N (∀ j, Z j) z) :
    pi (fun j => map (ContinuousMap.eval j) rfl a) = a := by
  refine Quotient.inductionOn a ?_
  intro p
  simp only [map_mk, pi_mk, GenLoop.pi_map_eval]
  rfl

/-- The homotopy group of an indexed product is the indexed product of the homotopy groups. -/
noncomputable def piEquiv (z : ∀ j, Z j) :
    HomotopyGroup N (∀ j, Z j) z ≃ ∀ j, HomotopyGroup N (Z j) (z j) where
  toFun a j := map (ContinuousMap.eval j) rfl a
  invFun := pi
  left_inv := pi_map_eval
  right_inv a := funext fun j => map_eval_pi a j

/-- The positive-dimensional multiplicative indexed-product equivalence. -/
noncomputable def piMulEquiv [DecidableEq N] [Nonempty N] (z : ∀ j, Z j) :
    HomotopyGroup N (∀ j, Z j) z ≃* ∀ j, HomotopyGroup N (Z j) (z j) :=
  { piEquiv z with
    map_mul' := fun a b => funext fun j =>
      map_mul (ContinuousMap.eval j) rfl a b }

end HomotopyGroup

end Submission
