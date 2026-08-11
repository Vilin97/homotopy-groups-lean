/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from the Tau Ceti project (https://github.com/TauCetiProject/TauCeti), Apache 2.0.
-/
import Mathlib.Topology.Homotopy.Lifting
import Submission.ForMathlib.HomotopyGroup.Map

/-!
# Higher homotopy groups and covering maps

A covering map induces an isomorphism on homotopy groups whose cube-index type has at least
two elements. Injectivity follows from uniqueness of homotopy lifts and surjectivity from
lifting along one cube coordinate.
-/

namespace Submission

open scoped unitInterval Topology Topology.Homotopy

private theorem zero_mem_cubeBoundary {N : Type*} [Nonempty N] :
    (0 : I^N) ∈ Cube.boundary N :=
  ⟨Classical.arbitrary N, Or.inl rfl⟩

namespace GenLoop

variable {N X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
  {p : E → X} {e : E}

/-- A covering map reflects homotopy of generalized loops. -/
@[simp]
theorem map_homotopic_iff [Nonempty N] (hp : IsCoveringMap p) {F G : Ω^ N E e} :
    _root_.GenLoop.Homotopic
        (map ⟨p, hp.continuous⟩ rfl F) (map ⟨p, hp.continuous⟩ rfl G) ↔
      _root_.GenLoop.Homotopic F G :=
  (hp.homotopicRel_iff_comp (f₀ := (F : C(I^N, E))) (f₁ := (G : C(I^N, E)))
    ⟨0, zero_mem_cubeBoundary,
      (_root_.GenLoop.boundary F 0 zero_mem_cubeBoundary).trans
        (_root_.GenLoop.boundary G 0 zero_mem_cubeBoundary).symm⟩).symm

/-- Every generalized loop of dimension at least two lifts at a prescribed point of a fibre. -/
theorem map_surjective [Nontrivial N] (hp : IsCoveringMap p) (f : Ω^ N X (p e)) :
    ∃ F : Ω^ N E e, map ⟨p, hp.continuous⟩ rfl F = f := by
  classical
  let i := Classical.arbitrary N
  let : Nonempty { j // j ≠ i } :=
    ⟨⟨(exists_ne i).choose, (exists_ne i).choose_spec⟩⟩
  let q : C(I × I^{ j // j ≠ i }, X) := (f : C(I^N, X)).comp (Cube.insertAt i)
  let cX : C(I^{ j // j ≠ i }, X) := .const _ (p e)
  let cE : C(I^{ j // j ≠ i }, E) := .const _ e
  let qRel : cX.HomotopyRel cX (Cube.boundary { j // j ≠ i }) :=
    { toContinuousMap := q
      map_zero_left := fun _ =>
        _root_.GenLoop.boundary f _ (Cube.insertAt_boundary i (Or.inl (Or.inl rfl)))
      map_one_left := fun _ =>
        _root_.GenLoop.boundary f _ (Cube.insertAt_boundary i (Or.inl (Or.inr rfl)))
      prop' := fun _ _ ha =>
        _root_.GenLoop.boundary f _ (Cube.insertAt_boundary i (Or.inr ha)) }
  let QRel : cE.HomotopyRel cE (Cube.boundary { j // j ≠ i }) :=
    hp.liftHomotopyRel qRel ⟨0, zero_mem_cubeBoundary, rfl⟩
      (funext fun _ => rfl) (funext fun _ => rfl)
  let P : Ω (Ω^ { j // j ≠ i } E e) _root_.GenLoop.const :=
    { toContinuousMap :=
        ⟨fun t => ⟨QRel.toContinuousMap.curry t, fun y hy => QRel.prop t y hy⟩,
          QRel.toContinuousMap.curry.continuous.subtype_mk _⟩
      source' := by ext y; exact QRel.apply_zero y
      target' := by ext y; exact QRel.apply_one y }
  let F : Ω^ N E e := _root_.GenLoop.fromLoop i P
  have hQ : p ∘ QRel.toContinuousMap = q := by
    simp only [QRel, IsCoveringMap.liftHomotopyRel]
    exact hp.liftHomotopy_lifts _ _ _
  have hF_apply (y : I^N) : F y = QRel (Cube.splitAt i y) := by
    rw [_root_.GenLoop.fromLoop_apply]
    rfl
  have hpF : ∀ y, p (F y) = f y := fun y => by
    calc
      p (F y) = p (QRel (Cube.splitAt i y)) := congr_arg p (hF_apply y)
      _ = q (Cube.splitAt i y) := congrFun hQ (Cube.splitAt i y)
      _ = f y := congr_arg f (Homeomorph.symm_apply_apply (Cube.splitAt i) y)
  exact ⟨F, _root_.GenLoop.ext _ _ hpF⟩

end GenLoop

namespace HomotopyGroup

variable {N X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
  {p : E → X} {e : E}

theorem map_injective [Nonempty N] (hp : IsCoveringMap p) :
    Function.Injective
      (map (N := N) (x := e) (y := p e) (⟨p, hp.continuous⟩ : C(E, X)) rfl) := by
  intro a b
  refine Quotient.inductionOn₂ a b fun F G h => ?_
  exact Quotient.sound ((GenLoop.map_homotopic_iff hp).1 (Quotient.exact h))

theorem map_surjective [Nontrivial N] (hp : IsCoveringMap p) :
    Function.Surjective
      (map (N := N) (x := e) (y := p e) (⟨p, hp.continuous⟩ : C(E, X)) rfl) := by
  refine Quotient.ind fun f => ?_
  obtain ⟨F, hF⟩ := GenLoop.map_surjective hp f
  exact ⟨⟦F⟧, by rw [map_mk, hF]⟩

/-- A covering map induces an isomorphism on every homotopy group of dimension at least two. -/
noncomputable def coveringMulEquiv [DecidableEq N] [Nontrivial N]
    (hp : IsCoveringMap p) (e : E) :
    HomotopyGroup N E e ≃* HomotopyGroup N X (p e) := by
  classical
  exact MulEquiv.ofBijective (mapHom (⟨p, hp.continuous⟩ : C(E, X)) rfl)
    ⟨map_injective hp, map_surjective hp⟩

end HomotopyGroup

end Submission
